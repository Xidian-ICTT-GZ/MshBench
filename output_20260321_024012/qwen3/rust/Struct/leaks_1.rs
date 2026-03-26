#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

//@ pred is_Spawnee<T>(unsafe fn(T), predicate(T)) = true;

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

//@ pred CountPulsesData_own(data: CountPulsesData, value: u32) =
//@   data.counter |-> ?counter &*& data.mutex |-> ?mutex &*&
//@   counter_own(counter, value) &*& mutex_own(mutex);

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
//@ req CountPulsesData_own(data, ?value);
//@ ens true;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    //@ open CountPulsesData_own(_,_); 
    loop {
        
        let done = wait_for_pulse(source);
        if done { break }
        //@ close mutex_own(mutex);
        let guard = acquire(mutex);
        //@ open mutex_own(mutex);
        //@ open counter_own(counter, value);
        *counter = (*counter).checked_add(1).unwrap();
        //@ let new_value = value + 1;
        //@ close counter_own(counter, new_value);
        //@ let value = new_value;
        release(guard);
        //@ close mutex_own(mutex);
    }
    //@ open counter_own(counter, _);
    //@ open mutex_own(mutex);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_own(counter, ?value) &*& mutex_own(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_own(data, value);
    
    
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

//@ pred PrintCountData_own(data: PrintCountData, value: u32) =
//@   data.counter |-> ?counter &*& data.mutex |-> ?mutex &*&
//@   counter_own(counter, value) &*& mutex_own(mutex);

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data, ?value);
//@ ens true;
{
    
    let PrintCountData { counter, mutex } = data;
    //@ open PrintCountData_own(_,_); 
    loop {
        
        thread::sleep(Duration::from_millis(1000));
        //@ close mutex_own(mutex);
        let guard = acquire(mutex);
        //@ open mutex_own(mutex);
        //@ open counter_own(counter, value);
        println!("{}", *counter);
        //@ close counter_own(counter, value);
        release(guard);
        //@ close mutex_own(mutex);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_own(counter, ?value) &*& mutex_own(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data, value);
    
    
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