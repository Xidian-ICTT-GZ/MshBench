#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

//@ predicate is_Mutex(Mutex* mutex) = true;
//@ predicate is_u32_ptr(u32* p; uint v) = *p |-> v;

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
//@ ensures result != 0;
//@ ensures is_Mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req is_Mutex(mutex);
//@ ensures true;
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req true;
//@ ensures true;
{}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req is_Mutex(data.mutex) &*& data.counter |-> ?v;
//@ ensures is_Mutex(data.mutex) &*& data.counter |-> _;
{
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open is_Mutex(mutex);
        let old_v = *counter;
        *counter = old_v.checked_add(1).unwrap();
        //@ close is_Mutex(mutex);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req is_Mutex(mutex) &*& counter |-> ?v;
//@ ensures true;
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req is_Mutex(data.mutex) &*& data.counter |-> ?v;
//@ ensures true;
{
    let PrintCountData { counter, mutex } = data;
    loop {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open is_Mutex(mutex);
        let v = *counter;
        println!("{}", v);
        //@ close is_Mutex(mutex);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req is_Mutex(mutex) &*& counter |-> ?v;
//@ ensures true;
{
    let data = PrintCountData { counter, mutex };
    spawn(print_count, data);
}

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close is_u32_ptr(counter, 0);
        
        let mutex = create_mutex();
        //@ close is_Mutex(mutex);
        
        print_count_async(counter, mutex);
        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}