#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@

pred is_Spawnee<T>(f: unsafe fn(arg: T), pre: pred(T)) = true;

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req true;
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
//@ ens true;
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
//@ req true;
//@ ens true;
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
//@ req true;
//@ ens true;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        //@ inv true;
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req true;
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
//@ req true;
//@ ens true;
{
    
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv true;
        
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        
        println!("{}", *counter);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req true;
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
        
        
        let mutex = create_mutex();
        
        print_count_async(counter, mutex);
        loop {
            //@ inv true;
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}