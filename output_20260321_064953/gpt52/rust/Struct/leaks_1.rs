#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@

pred counter_ptr(p: *mut u32) = p as usize != 0;

pred mutex_ptr(p: *mut Mutex) = p as usize != 0;

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
//@ ens mutex_ptr(result);
//@ assume_correct
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
//@ req mutex_ptr(mutex);
//@ ens true;
//@ assume_correct
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req true;
//@ ens true;
//@ assume_correct
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
//@ req counter_ptr(data.counter) &*& mutex_ptr(data.mutex);
//@ ens true;
//@ assume_correct
{
    
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        //@ assert counter_ptr(counter);
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_ptr(counter) &*& mutex_ptr(mutex);
//@ ens true;
//@ assume_correct
{
    let data = CountPulsesData { counter, mutex, source };
    
    
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req counter_ptr(data.counter) &*& mutex_ptr(data.mutex);
//@ ens true;
//@ assume_correct
{
    
    let PrintCountData { counter, mutex } = data;
    loop {
        
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        
        //@ assert counter_ptr(counter);
        println!("{}", *counter);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_ptr(counter) &*& mutex_ptr(mutex);
//@ ens true;
//@ assume_correct
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
        
        
        let mutex = create_mutex();
        
        //@ close counter_ptr(counter);
        //@ close mutex_ptr(mutex);
        print_count_async(counter, mutex);
        loop {
            
            let source = wait_for_source();
            //@ close counter_ptr(counter);
            //@ close mutex_ptr(mutex);
            count_pulses_async(counter, mutex, source);
        }
    }
}