use std::alloc::{alloc, handle_alloc_error, Layout};

#[pred]
predicate mutex_inv(mutex: *mut Mutex) = 
    mutex |-> ?m &*& m == Mutex::new(());

#[pred]
predicate mutex_guard(guard: MutexGuard) = 
    guard |-> ?g &*& g == MutexGuard::new();

#[pred]
predicate counter_pred(counter: *mut u32, value: u32) =
    counter |-> value;

#[pred]
predicate count_pulses_data_pred(data: CountPulsesData, counter_val: u32) =
    data.counter |-> counter_val &*& mutex_inv(data.mutex) &*& data.source |-> ?_source;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
#[requires true]
#[ensures true]
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
#[requires true]
#[ensures mutex_inv(result);]
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
#[requires mutex_inv(mutex)]
#[ensures mutex_inv(mutex) &*& mutex_guard(result)]
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
#[requires mutex_guard(guard)]
#[ensures true]
{
    drop(guard);
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

unsafe fn count_pulses(data: CountPulsesData)
#[requires count_pulses_data_pred(data, ?c)]
#[ensures false;] // diverges
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    let mut v = c;
    
    loop
    #[invariant count_pulses_data_pred(data, v) &*& 0 <= v]
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        // We have exclusive access to counter via mutex
        *counter = v.checked_add(1).unwrap();
        v = v + 1;

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
#[requires counter |-> ?c &*& mutex_inv(mutex)]
#[ensures counter |-> c &*& mutex_inv(mutex)]
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

fn main()
#[requires true]
#[ensures true]
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop
        #[invariant counter |-> ?v &*& mutex_inv(mutex) &*& 0 <= v]
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);

            print_u32(count);
        }
    }
}