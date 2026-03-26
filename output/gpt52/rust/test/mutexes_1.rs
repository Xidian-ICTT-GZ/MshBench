use std::alloc::{Layout, alloc, handle_alloc_error};

pred counter(p: *mut u32; v: u32) = *p |-> v;

pred mutex_cell(p: *mut Mutex; m: Mutex) = *p |-> m;

pred mutex_ptr(p: *mut Mutex) = mutex_cell(p, _);

pred mutex_guard(g: MutexGuard; mutex: *mut Mutex) = true;

pred CountPulsesData_pred(d: CountPulsesData; counterp: *mut u32, mutexp: *mut Mutex, source: i32) =
    d.counter |-> counterp &*& d.mutex |-> mutexp &*& d.source |-> source;

pred sendable<T>(s: Sendable<T>; pay: T) = s.payload |-> pay;

pred thread_arg_token<T>(arg: T) = false;

unsafe impl<T> Send for Sendable<T> {}

#[requires(true)]
#[ensures(true)]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[requires(true)]
#[ensures(mutex_ptr(result))]
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex_ptr(mutex))]
#[ensures(mutex_ptr(mutex) &*& mutex_guard(result, mutex))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    (*mutex).lock().unwrap()
}

#[requires(mutex_ptr(_mutex) &*& mutex_guard(guard, _mutex))]
#[ensures(mutex_ptr(_mutex))]
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
}

#[requires(true)]
#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32)
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u32(n: u32)
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires(counter(counter, _) &*& mutex_ptr(mutex))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        #[invariant(counter(counter, _) &*& mutex_ptr(mutex))]
        {
            wait_for_pulse(source);
            let guard = acquire(mutex);

            *counter = (*counter).checked_add(1).unwrap();

            release(guard);
        }
    }
}

#[requires(counter(counter, _) &*& mutex_ptr(mutex))]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    let data = CountPulsesData { counter, mutex, source };

    spawn(count_pulses, data);
}

#[requires(true)]
#[ensures(true)]
fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;

        //@ close counter(counter, 0);

        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            #[invariant(counter(counter, _) &*& mutex_ptr(mutex))]
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