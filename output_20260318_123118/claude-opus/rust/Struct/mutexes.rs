use std::alloc::{Layout, alloc, handle_alloc_error};

predicate mutex(Mutex *mutex; )
    = mutex != 0 &*& *mutex |-> _;

predicate mutex_guard(MutexGuard guard; Mutex *mutex)
    = true; 

predicate counter_uint32(u32 *counter; int count)
    = counter != 0 &*& *counter |-> ?v &*& v == count as u32;

predicate count_pulses_data(CountPulsesData data; int count)
    = counter_uint32(data.counter, count) &*& mutex(data.mutex);

#[trusted]
unsafe fn create_mutex() -> *mut Mutex
    #[ensures mutex(result)]
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[trusted]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
    #[requires mutex(mutex)]
    #[ensures mutex_guard(result, mutex)]
{
    (*mutex).lock().unwrap()
}

#[trusted]
unsafe fn release(guard: MutexGuard)
    #[requires mutex_guard(guard, _)]
    #[ensures true]
{
    drop(guard);
}

#[predicate]
fn is_Spawnee<T>(f: unsafe fn(arg: T), pred: fn(arg: T) -> bool) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
    #[requires exists<pred: fn(T) -> bool>([_]is_Spawnee(f, pred) &*& pred(arg))]
    #[ensures true]
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

unsafe fn wait_for_pulse(_source: i32)
    #[requires true]
    #[ensures true]
{
    std::thread::sleep(std::time::Duration::from_millis(500)); 
}

unsafe fn print_u32(n: u32)
    #[requires true]
    #[ensures true]
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

predicate count_pulses_data_pred(CountPulsesData data; int count) =
    counter_uint32(data.counter, count) &*& mutex(data.mutex);

unsafe fn count_pulses(data: CountPulsesData)
    #[requires count_pulses_data_pred(data, ?count)]
    #[ensures true] 
{
    let CountPulsesData { counter, mutex, source } = data;
    let mut local_count = count;
    loop {
        #[invariant count_pulses_data_pred(data, local_count)]
        {
            wait_for_pulse(source);
            let guard = acquire(mutex);
            *counter = (*counter).checked_add(1).unwrap();
            local_count = local_count + 1;
            release(guard);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
    #[requires counter_uint32(counter, ?count) &*& mutex(mutex)]
    #[ensures true]
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            #[invariant counter_uint32(counter, ?count) &*& mutex(mutex)]
            {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                let guard = acquire(mutex);
                let count = *counter;
                release(guard);
                print_u32(count);
            }
        }
    }
}