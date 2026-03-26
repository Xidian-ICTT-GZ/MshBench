#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
pred Mutex_own(mutex: *mut Mutex;);

pred CountPulsesData_own(counter: *mut u32, mutex: *mut Mutex, source: i32) =
    Mutex_own(mutex) &*& (*counter) |-> _;

pred PrintCountData_own(counter: *mut u32, mutex: *mut Mutex) =
    Mutex_own(mutex) &*& (*counter) |-> _;

pred thread_spawned(f: unsafe fn(*mut u8), arg: *mut u8;);
@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req true;
//@ ens thread_spawned(transmute(f), transmute(Box::into_raw(Box::new(arg))));
{
    let package = Sendable { payload: arg };
    let boxed = Box::new(package);
    let raw = Box::into_raw(boxed);
    thread::spawn(move || {
        let package_moved = *Box::from_raw(raw as *mut Sendable<T>);
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens Mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    //@ assume(Mutex_own(mutex));
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req Mutex_own(mutex);
//@ ens Mutex_own(mutex);
{
    (&*mutex).lock().unwrap()
}

unsafe fn release(_guard: MutexGuard)
//@ req true;
//@ ens true;
{
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{
    true
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{
    1
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req Mutex_own(data.mutex) &*& (*data.counter) |-> _;
//@ ens true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    loop {
        //@ inv Mutex_own(mutex) &*& (*counter) |-> _;
        let done = wait_for_pulse(source);
        if done {
            //@ leak Mutex_own(mutex);
            //@ leak (*counter) |-> _;
            break;
        }
        let guard = acquire(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req Mutex_own(mutex) &*& (*counter) |-> _;
//@ ens thread_spawned(transmute(count_pulses as unsafe fn(CountPulsesData)), transmute(0 as *mut u8));
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
//@ req Mutex_own(data.mutex) &*& (*data.counter) |-> _;
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv Mutex_own(mutex) &*& (*counter) |-> _;
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        println!("{}", *counter);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req Mutex_own(mutex) &*& (*counter) |-> _;
//@ ens thread_spawned(transmute(print_count as unsafe fn(PrintCountData)), transmute(0 as *mut u8));
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
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);
        //@ assume(false);
        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}