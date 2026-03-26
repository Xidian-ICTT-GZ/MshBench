#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn is_Spawnee<T>(f: unsafe fn(arg: T), pre: fn(&T) -> bool) -> bool { true }

#[predicate]
fn Sendable_own<T>(s: &Sendable<T>, pre: fn(&T) -> bool) -> bool { pre(&s.payload) }

#[predicate]
fn u32_own(p: *mut u32, v: u32) -> bool { true }

#[predicate]
fn Mutex_own(p: *mut Mutex) -> bool { true }

#[predicate]
fn Mutex_guard_own(g: MutexGuard, p: *mut Mutex) -> bool { true }

#[predicate]
fn CountPulsesData_own(d: &CountPulsesData) -> bool { 
    u32_own(d.counter, ?c) &*& Mutex_own(d.mutex) 
}

#[predicate]
fn PrintCountData_own(d: &PrintCountData) -> bool { 
    u32_own(d.counter, ?c) &*& Mutex_own(d.mutex) 
}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(&arg);
//@ ens true;
{
    let package = Sendable { payload: arg };
    //@ close Sendable_own(&package, pre);
    thread::spawn(move || {
        let package_moved = package;
        //@ open Sendable_own(&package_moved, pre);
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
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close Mutex_own(mutex);
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req Mutex_own(mutex);
//@ ens Mutex_guard_own(result, mutex);
{
    //@ open Mutex_own(mutex);
    let guard = (&*mutex).lock().unwrap();
    //@ close Mutex_guard_own(guard, mutex);
    guard
}

unsafe fn release(_guard: MutexGuard)
//@ req Mutex_guard_own(_guard, ?mutex);
//@ ens Mutex_own(mutex);
{
    //@ open Mutex_guard_own(_guard, mutex);
    //@ close Mutex_own(mutex);
}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(&data);
//@ ens false;
{
    //@ open CountPulsesData_own(&data);
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        //@ invariant u32_own(counter, ?c) &*& Mutex_own(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open u32_own(counter, c);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close u32_own(counter, c + 1);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req u32_own(counter, ?c) &*& Mutex_own(mutex);
//@ ens false;
{
    //@ close CountPulsesData_own(&CountPulsesData { counter, mutex, source });
    let data = CountPulsesData { counter, mutex, source };
    //@ close exists(CountPulsesData_own);
    //@ close is_Spawnee(count_pulses, CountPulsesData_own);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(&data);
//@ ens false;
{
    //@ open PrintCountData_own(&data);
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ invariant u32_own(counter, ?c) &*& Mutex_own(mutex);
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open u32_own(counter, c);
        println!("{}", *counter);
        //@ close u32_own(counter, c);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req u32_own(counter, ?c) &*& Mutex_own(mutex);
//@ ens false;
{
    //@ close PrintCountData_own(&PrintCountData { counter, mutex });
    let data = PrintCountData { counter, mutex };
    //@ close exists(PrintCountData_own);
    //@ close is_Spawnee(print_count, PrintCountData_own);
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens false;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close u32_own(counter, 0);
        
        let mutex = create_mutex();
        
        print_count_async(counter, mutex);
        loop {
            //@ invariant false;
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}