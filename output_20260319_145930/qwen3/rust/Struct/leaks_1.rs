#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@ pred CountPulsesData_own(t: thread_id_t, counter: *mut u32, mutex: *mut Mutex, source: i32) =
    [_]is_Spawnee(count_pulses, ?pre) &*& pre(CountPulsesData { counter, mutex, source }); @*/

/*@ pred PrintCountData_own(t: thread_id_t, counter: *mut u32, mutex: *mut Mutex) =
    [_]is_Spawnee(print_count, ?pre) &*& pre(PrintCountCountData { counter, mutex }); @*/

/*@ pred counter_block(counter: *mut u32; v: u32) =
    alloc_block(counter, std::mem::size_of::<u32>()) &*& *counter |-> v; @*/

/*@ pred mutex_block(mutex: *mut Mutex) =
    alloc_block(mutex, std::mem::size_of::<Mutex>()) &*& (*mutex).lock() |-> _; @*/

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
//@ ens mutex_block(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close alloc_block(mutex, std::mem::size_of::<Mutex>());
    mutex.write(Mutex::new(()));
    //@ close mutex_block(mutex);
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

/*@ pred CountPulsesData_pred(data: CountPulsesData) =
    counter_block(data.counter, ?v) &*& mutex_block(data.mutex); @*/

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_block(mutex);
//@ ens mutex_block(mutex) &*& true;
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req true;
//@ ens true;
{}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_pred(data);
//@ ens true;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    //@ open CountPulsesData_pred(_);
    loop {
        //@ inv counter_block(counter, ?v) &*& mutex_block(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
    //@ close counter_block(counter, _);
    //@ close mutex_block(mutex);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_block(counter, ?v) &*& mutex_block(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_pred(data);
    //@ assert [_]is_Spawnee(count_pulses, ?pre) &*& pre(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@ pred PrintCountData_pred(data: PrintCountData) =
    counter_block(data.counter, ?v) &*& mutex_block(data.mutex); @*/

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_pred(data);
//@ ens true;
{
    
    let PrintCountData { counter, mutex } = data;
    //@ open PrintCountData_pred(_);
    loop {
        //@ inv counter_block(counter, ?v) &*& mutex_block(mutex);
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        
        println!("{}", *counter);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_block(counter, ?v) &*& mutex_block(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_pred(data);
    //@ assert [_]is_Spawnee(print_count, ?pre) &*& pre(data);
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        //@ close alloc_block(counter, std::mem::size_of::<u32>());
        *counter = 0;
        //@ close counter_block(counter, 0);
        
        
        let mutex = create_mutex();
        //@ assert mutex_block(mutex);
        
        print_count_async(counter, mutex);
        loop {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}