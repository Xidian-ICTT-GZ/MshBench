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
//@ ens result as usize != 0 &*& mutex(result, false);
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
//@ req mutex(mutex, false);
//@ ens mutex(mutex, true) &*& guard(result, mutex);
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req guard(_guard, ?mutex) &*& mutex(mutex, true);
//@ ens mutex(mutex, false);
{}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data(data);
//@ ens true;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter as usize != 0 &*& [?q]u32_own(counter, _) &*& mutex(mutex, false) &*& source >= 0;
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req print_count_data(data);
//@ ens true;
{
    
    let PrintCountData { counter, mutex } = data;
    loop {
        
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        
        println!("{}", *counter);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter as usize != 0 &*& [?q]u32_own(counter, _) &*& mutex(mutex, false);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close print_count_data(data);
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
        //@ close u32_own(counter, 0);
        //@ close u32_own(counter, 0);
        
        let mutex = create_mutex();
        
        print_count_async(counter, mutex);
        loop {
            
            let source = wait_for_source();
            //@ assert source >= 0;
            count_pulses_async(counter, mutex, source);
        }
    }
}

/*@
predicate mutex(*mut Mutex mutex, bool held) = 
    struct_Mutex_padding(mutex) &*& mutex |-> ?inner &*& held ? inner |-> ?v : true;

predicate guard(MutexGuard guard, *mut Mutex mutex) = true;

predicate u32_own(*mut u32 ptr, u32 v) = 
    integer(ptr, v);

predicate count_pulses_data(CountPulsesData data) = 
    data.counter as usize != 0 &*& [?q]u32_own(data.counter, _) &*& mutex(data.mutex, false) &*& data.source >= 0;

predicate print_count_data(PrintCountData data) = 
    data.counter as usize != 0 &*& [?q]u32_own(data.counter, _) &*& mutex(data.mutex, false);
@*/