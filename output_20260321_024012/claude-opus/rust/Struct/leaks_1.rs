#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

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
//@ ensures mutex_handle(result);
//@ terminates;
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
//@ req mutex_handle(mutex);
//@ ensures mutex_handle(mutex) &*& [_]mutex_guard(result);
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req [_]mutex_guard(_guard);
//@ ensures true;
{}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req data_valid_count_pulses(data.counter, data.mutex);
//@ ensures true;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        //@ open data_valid_count_pulses(counter, mutex);
        let old = *counter;
        *counter = (*counter).checked_add(1).unwrap();
        //@ close data_valid_count_pulses(counter, mutex);
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req data_valid_count_pulses(counter, mutex);
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
//@ req data_valid_print_count(data.counter, data.mutex);
//@ ensures true;
{
    
    let PrintCountData { counter, mutex } = data;
    loop {
        
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open data_valid_print_count(counter, mutex);
        
        println!("{}", *counter);
        
        //@ close data_valid_print_count(counter, mutex);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req data_valid_print_count(counter, mutex);
//@ ensures true;
{
    let data = PrintCountData { counter, mutex };
    
    
    spawn(print_count, data);
}

predicate mutex_handle(Mutex *m) = [_]m.lock().is_ok();
predicate mutex_guard(MutexGuard g) = true;

predicate data_valid_count_pulses(u32 *counter, Mutex *mutex) = mutex_handle(mutex) &*& *counter |-> _ &*& [_]mutex_guard(?g);
predicate data_valid_print_count(u32 *counter, Mutex *mutex) = mutex_handle(mutex) &*& *counter |-> _ &*& [_]mutex_guard(?g);

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close data_valid_count_pulses(counter, ?mutex);
        //@ close data_valid_print_count(counter, mutex);
        
        
        let mutex = create_mutex();
        
        print_count_async(counter, mutex);
        loop {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}