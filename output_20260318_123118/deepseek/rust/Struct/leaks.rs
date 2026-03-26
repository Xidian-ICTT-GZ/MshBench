#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ predicate mutex_handle(*mut Mutex) = true;
//@ predicate mutex_guard(MutexGuard) = true;
//@ predicate counter_handle(*mut u32) = true;
//@ predicate spawnee_pre<T>(unsafe fn(arg: T), T) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req spawnee_pre(f, arg);
//@ ens true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_handle(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_handle(mutex);
//@ ens mutex_guard(result) &*& mutex_handle(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(guard);
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

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_handle(data.counter) &*& mutex_handle(data.mutex);
//@ ens true;
{
    let CountPulsesData {counter, mutex, source} = data;
    
    loop {
        //@ invariant counter_handle(counter) &*& mutex_handle(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_handle(counter) &*& mutex_handle(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close spawnee_pre(count_pulses, data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req counter_handle(data.counter) &*& mutex_handle(data.mutex);
//@ ens true;
{
    let PrintCountData {counter, mutex} = data;
    loop {
        //@ invariant counter_handle(counter) &*& mutex_handle(mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        print_u32(*counter);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_handle(counter) &*& mutex_handle(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close spawnee_pre(print_count, data);
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
        //@ close counter_handle(counter);
        
        let mutex = create_mutex();
        //@ close counter_handle(counter);
        //@ close mutex_handle(mutex);
        print_count_async(counter, mutex);
        
        loop {
            //@ invariant counter_handle(counter) &*& mutex_handle(mutex);
            let source = wait_for_source();
            //@ close counter_handle(counter);
            //@ close mutex_handle(mutex);
            count_pulses_async(counter, mutex, source);
        }
    }
}