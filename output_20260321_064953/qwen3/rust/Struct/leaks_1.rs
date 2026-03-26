#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

//@ pred is_Spawnee<T>(unsafe fn(T), pred(T)) = true;

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

//@ pred mutex_own(mutex: *mut Mutex) = true;
//@ pred counter_own(counter: *mut u32, value: u32) = *counter |-> value;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_own(mutex);
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ pred count_pulses_data(counter: *mut u32, mutex: *mut Mutex, source: i32) =
//@   counter_own(counter, ?v) &*& mutex_own(mutex);

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex);
//@ ens mutex_own(mutex);
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
{ true }
unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{ 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data(data.counter, data.mutex, data.source);
//@ ens true;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        
        let done = wait_for_pulse(source);
        if done { break }
        //@ open count_pulses_data(counter, mutex, source);
        let guard = acquire(mutex);
        //@ open counter_own(counter, ?v);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_own(counter, v + 1);
        release(guard);
        //@ close count_pulses_data(counter, mutex, source);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_own(counter, ?v) &*& mutex_own(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data(counter, mutex, source);
    
    
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

//@ pred print_count_data(counter: *mut u32, mutex: *mut Mutex) =
//@   counter_own(counter, ?v) &*& mutex_own(mutex);

unsafe fn print_count(data: PrintCountData)
//@ req print_count_data(data.counter, data.mutex);
//@ ens true;
{
    
    let PrintCountData { counter, mutex } = data;
    loop {
        
        thread::sleep(Duration::from_millis(1000));
        //@ open print_count_data(counter, mutex);
        let guard = acquire(mutex);
        //@ open counter_own(counter, ?v);
        println!("{}", *counter);
        //@ close counter_own(counter, v);
        release(guard);
        //@ close print_count_data(counter, mutex);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_own(counter, ?v) &*& mutex_own(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close print_count_data(counter, mutex);
    
    
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
        //@ close counter_own(counter, 0);
        
        
        let mutex = create_mutex();
        //@ assert mutex_own(mutex);
        
        print_count_async(counter, mutex);
        loop {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}