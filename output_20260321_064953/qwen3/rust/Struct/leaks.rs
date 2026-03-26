#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

//@ pred is_Spawnee<T>(unsafe fn(T), predicate(T)) = true;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

//@ pred mutex_own(mutex: *mut Mutex;);

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

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex);
//@ ens true;
{
    //@ open mutex_own(mutex);
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
//@ ens true;
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ pred counter_own(counter: *mut u32;);

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_own(data.counter) &*& mutex_own(data.mutex);
//@ ens true;
{
    
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        
        let done = wait_for_pulse(source);
        if done { break }
        //@ close mutex_own(mutex);
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
        //@ open mutex_own(mutex);
    }
    //@ open counter_own(counter);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_own(counter) &*& mutex_own(mutex);
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
//@ req counter_own(data.counter) &*& mutex_own(data.mutex);
//@ ens true;
{
    
    let PrintCountData {counter, mutex} = data;
    loop {
        
        std::thread::sleep(std::time::Duration::from_millis(1000));
        //@ close mutex_own(mutex);
        let guard = acquire(mutex);
        
        print_u32(*counter);
        
        release(guard);
        //@ open mutex_own(mutex);
    }
    //@ open counter_own(counter);
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_own(counter) &*& mutex_own(mutex);
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
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close counter_own(counter);
        
        
        let mutex = create_mutex();
        

        print_count_async(counter, mutex);

        loop {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}