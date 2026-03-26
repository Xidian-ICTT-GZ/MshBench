#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

//@ predicate is_Spawnee(f: *const (), pre: *const ()) = true;
//@ predicate mutex_inv(m: *mut std::sync::Mutex<()>) = m != std::ptr::null_mut();
//@ predicate counter_owned(c: *mut u32) = c != std::ptr::null_mut();

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
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
//@ ensures mutex_inv(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ requires mutex_inv(mutex);
//@ ensures true;
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ requires true;
//@ ensures true;
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
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

unsafe fn count_pulses(data: CountPulsesData)
//@ requires counter_owned(data.counter) &*& mutex_inv(data.mutex);
//@ ensures true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        //@ invariant counter_owned(counter) &*& mutex_inv(mutex);
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ requires counter_owned(counter) &*& mutex_inv(mutex);
//@ ensures true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ requires counter_owned(data.counter) &*& mutex_inv(data.mutex);
//@ ensures true;
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ invariant counter_owned(counter) &*& mutex_inv(mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        print_u32(*counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ requires counter_owned(counter) &*& mutex_inv(mutex);
//@ ensures true;
{
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main() {
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