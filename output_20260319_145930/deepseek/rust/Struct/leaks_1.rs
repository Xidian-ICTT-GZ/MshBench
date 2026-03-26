#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@
pred mutex_own(?m: *mut Mutex) = true;
pred mutex_guard_own(?g: MutexGuard) = true;
pred counter_own(?c: *mut u32) = true;
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
//@ ens mutex_own(result);
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
//@ req mutex_own(mutex);
//@ ens mutex_own(mutex) &*& mutex_guard_own(result);
{
    (&*mutex).lock().unwrap()
}

unsafe fn release(_guard: MutexGuard)
//@ req mutex_guard_own(_guard);
//@ ens true;
{
}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_own(data.counter) &*& mutex_own(data.mutex);
//@ ens counter_own(data.counter) &*& mutex_own(data.mutex);
{
    let CountPulsesData { counter, mutex, source } = data;
    loop
    //@ inv counter_own(counter) &*& mutex_own(mutex);
    {
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open mutex_own(mutex);
        //@ close mutex_own(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
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
//@ ens counter_own(data.counter) &*& mutex_own(data.mutex);
{
    let PrintCountData { counter, mutex } = data;
    loop
    //@ inv counter_own(counter) &*& mutex_own(mutex);
    {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex_own(mutex);
        //@ close mutex_own(mutex);
        println!("{}", *counter);
        release(guard);
    }
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
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter_own(counter);
        
        let mutex = create_mutex();
        //@ close mutex_own(mutex);
        
        print_count_async(counter, mutex);
        loop
        //@ inv counter_own(counter) &*& mutex_own(mutex);
        {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}