use std::alloc::{Layout, alloc, handle_alloc_error};

//@ pred mutex_inv(m: *mut Mutex);

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}
unsafe fn spawn<T: ’static>(f: unsafe fn(arg: T), arg: T)
//@ requires true;
//@ ensures true;
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
//@ requires true;
//@ ensures result != std::ptr::null_mut() &*& mutex_inv(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_inv(mutex);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ requires mutex_inv(mutex);
//@ ensures mutex_inv(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ requires true;
//@ ensures true;
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ requires true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
//@ requires true;
//@ ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ pred valid_counter(counter: *mut u32) = counter != std::ptr::null_mut();

unsafe fn count_pulses(data: CountPulsesData)
//@ requires valid_counter(data.counter) &*& mutex_inv(data.mutex);
//@ ensures mutex_inv(data.mutex);
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_inv(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close mutex_inv(mutex);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ requires valid_counter(counter) &*& mutex_inv(mutex);
//@ ensures true;
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
        //@ close valid_counter(counter);

        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_inv(mutex);
            let count = *counter;
            //@ close mutex_inv(mutex);
            release(guard);
            print_u32(count);
        }
    }
}