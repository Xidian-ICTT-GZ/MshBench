#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@

pred mutex_raw(m: *mut Mutex) = true;
pred counter_raw(c: *mut u32) = true;

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
{
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens result != std::ptr::null_mut() &*& mutex_raw(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_raw(mutex);
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_raw(mutex);
//@ ens mutex_raw(mutex);
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req true;
//@ ens true;
{}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
//@ assume_correct
{ true }
unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
//@ assume_correct
{ 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_raw(data.counter) &*& mutex_raw(data.mutex);
//@ ens true;
{
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        //@ inv counter_raw(counter) &*& mutex_raw(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_raw(counter) &*& mutex_raw(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };

    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req counter_raw(data.counter) &*& mutex_raw(data.mutex);
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv counter_raw(counter) &*& mutex_raw(mutex);
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);

        println!("{}", *counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_raw(counter) &*& mutex_raw(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter_raw(counter);

        let mutex = create_mutex();

        print_count_async(counter, mutex);
        loop {
            //@ inv counter_raw(counter) &*& mutex_raw(mutex);
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}