#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

predicate_ctor is_Spawnee<T>(unsafe fn(T) -> (), predicate(T))();

predicate counter(u32* c; u32 v) = *c |-> v;
predicate mutex(Mutex* m) = *m |-> _;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

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
//@ ens mutex(result);
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

predicate count_pulses_data(CountPulsesData data; u32 v) =
    counter(data.counter, v) &*& mutex(data.mutex);

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex(mutex);
//@ ens mutex(mutex) &*& [_]mutex_guard(mutex);
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req [_]mutex_guard(?mutex) &*& mutex(mutex);
//@ ens mutex(mutex);
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
//@ req count_pulses_data(data, ?v);
//@ ens count_pulses_data(data, ?w) &*& w >= v;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    loop
    //@ inv count_pulses_data(CountPulsesData { counter, mutex, source }, ?cur) &*& cur >= v;
    {
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter(counter, ?v) &*& mutex(mutex);
//@ ens counter(counter, v) &*& mutex(mutex);
{
    let data = CountPulsesData { counter, mutex, source };
    
    
    spawn(count_pulses, data);
    //@ close is_Spawnee(count_pulses, count_pulses_data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

predicate print_count_data(PrintCountData data) =
    counter(data.counter, ?v) &*& mutex(data.mutex);

unsafe fn print_count(data: PrintCountData)
//@ req print_count_data(data);
//@ ens print_count_data(data);
{
    
    let PrintCountData { counter, mutex } = data;
    loop
    //@ inv print_count_data(PrintCountData { counter, mutex });
    {
        
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        
        println!("{}", *counter);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter(counter, ?v) &*& mutex(mutex);
//@ ens counter(counter, v) &*& mutex(mutex);
{
    let data = PrintCountData { counter, mutex };
    
    
    spawn(print_count, data);
    //@ close is_Spawnee(print_count, print_count_data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter(counter, 0);
        
        
        let mutex = create_mutex();
        //@ assert mutex(mutex);
        
        print_count_async(counter, mutex);
        loop {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}