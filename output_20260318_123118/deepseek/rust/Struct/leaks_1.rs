#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn is_Spawnee<T>(f: unsafe fn(arg: T), pre: Predicate<T>) -> bool { true }

#[predicate]
fn Spawnee_pre<T>(arg: T) -> bool { true }

#[predicate]
fn mutex_handle(mutex: *mut Mutex) -> bool { true }

#[predicate]
fn mutex_frac(mutex: *mut Mutex, frac: u32) -> bool { true }

#[predicate]
fn mutex_guard(guard: MutexGuard, mutex: *mut Mutex) -> bool { true }

#[predicate]
fn counter_handle(counter: *mut u32) -> bool { true }

#[predicate]
fn counter_frac(counter: *mut u32, frac: u32) -> bool { true }

#[predicate]
fn counter_full(counter: *mut u32) -> bool { true }

#[predicate]
fn mutex_full(mutex: *mut Mutex) -> bool { true }

#[predicate]
fn mutex_shared(mutex: *mut Mutex) -> bool { true }

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
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
//@ ens mutex_handle(result) &*& mutex_full(result);
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
//@ req mutex_frac(mutex, 1) &*& mutex_shared(mutex);
//@ ens mutex_guard(result, mutex);
{
    (&*mutex).lock().unwrap()
}

unsafe fn release(_guard: MutexGuard) 
//@ req mutex_guard(_guard, ?mutex);
//@ ens mutex_frac(mutex, 1) &*& mutex_shared(mutex);
{}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_frac(data.counter, 1) &*& mutex_frac(data.mutex, 1) &*& mutex_shared(data.mutex);
//@ ens counter_frac(data.counter, 1) &*& mutex_frac(data.mutex, 1) &*& mutex_shared(data.mutex);
{
    let CountPulsesData { counter, mutex, source } = data;
    loop
    //@ inv counter_frac(counter, 1) &*& mutex_frac(mutex, 1) &*& mutex_shared(mutex);
    {
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open mutex_guard(guard, mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_frac(counter, 1) &*& mutex_frac(mutex, 1) &*& mutex_shared(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close is_Spawnee(count_pulses, Spawnee_pre);
    //@ close Spawnee_pre(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req counter_frac(data.counter, 1) &*& mutex_frac(data.mutex, 1) &*& mutex_shared(data.mutex);
//@ ens counter_frac(data.counter, 1) &*& mutex_frac(data.mutex, 1) &*& mutex_shared(data.mutex);
{
    let PrintCountData { counter, mutex } = data;
    loop
    //@ inv counter_frac(counter, 1) &*& mutex_frac(mutex, 1) &*& mutex_shared(mutex);
    {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex_guard(guard, mutex);
        println!("{}", *counter);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_frac(counter, 1) &*& mutex_frac(mutex, 1) &*& mutex_shared(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close is_Spawnee(print_count, Spawnee_pre);
    //@ close Spawnee_pre(data);
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
        //@ close counter_full(counter);
        //@ close counter_frac(counter, 1);
        //@ close counter_frac(counter, 1);
        
        let mutex = create_mutex();
        //@ close mutex_shared(mutex);
        //@ close mutex_frac(mutex, 1);
        //@ close mutex_frac(mutex, 1);
        
        print_count_async(counter, mutex);
        loop
        //@ inv counter_frac(counter, 1) &*& mutex_frac(mutex, 1) &*& mutex_shared(mutex);
        {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}