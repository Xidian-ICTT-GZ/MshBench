#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

// verifast_options{}

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ensures true;
//@ assume_correct
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
//@ req true;
//@ ensures true;
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex != std::ptr::null_mut();
//@ ensures true;
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
//@ ensures true;
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

// We require that counter and mutex pointers are valid and mutable.
unsafe fn count_pulses(data: CountPulsesData)
//@ req data.counter != std::ptr::null_mut() &*& data.mutex != std::ptr::null_mut();
//@ ensures true;
{
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);

        // Safe to dereference counter because of req.
        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter != std::ptr::null_mut() &*& mutex != std::ptr::null_mut();
//@ ensures true;
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

// Require valid pointers.
unsafe fn print_count(data: PrintCountData)
//@ req data.counter != std::ptr::null_mut() &*& data.mutex != std::ptr::null_mut();
//@ ensures true;
{
    let PrintCountData {counter, mutex} = data;
    loop {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        print_u32(*counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter != std::ptr::null_mut() &*& mutex != std::ptr::null_mut();
//@ ensures true;
{
    let data = PrintCountData { counter, mutex };
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ensures true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);

        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}