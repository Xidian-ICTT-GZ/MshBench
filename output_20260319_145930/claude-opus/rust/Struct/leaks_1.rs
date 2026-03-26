#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@

pred Mutex(mutex: *mut Mutex;);

pred Counter(counter: *mut u32, mutex: *mut Mutex;) =
    [1/2](*counter |-> _) &*& [1/2]Mutex(mutex);

pred CountPulsesData_own(data: CountPulsesData;) =
    Counter(data.counter, data.mutex);

pred PrintCountData_own(data: PrintCountData;) =
    Counter(data.counter, data.mutex);

pred_ctor count_pulses_pre()(data: CountPulsesData) =
    CountPulsesData_own(data);

pred_ctor print_count_pre()(data: PrintCountData) =
    PrintCountData_own(data);

lem count_pulses_Spawnee()
    req true;
    ens [_]is_Spawnee(count_pulses, count_pulses_pre);
{
    assume(false);
}

lem print_count_Spawnee()
    req true;
    ens [_]is_Spawnee(print_count, print_count_pre);
{
    assume(false);
}

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
//@ ens Mutex(result);
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

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]Mutex(mutex);
//@ ens [f]Mutex(mutex);
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
//@ req CountPulsesData_own(data);
//@ ens true;
{
    //@ open CountPulsesData_own(data);
    //@ open Counter(data.counter, data.mutex);
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        //@ inv [1/2](*counter |-> _) &*& [1/2]Mutex(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req Counter(counter, mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_own(data);
    //@ close count_pulses_pre()(data);
    //@ count_pulses_Spawnee();
    spawn(count_pulses, data);
}

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ens true;
//@ assume_correct
{
    //@ open PrintCountData_own(data);
    //@ open Counter(data.counter, data.mutex);
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv [1/2](*counter |-> _) &*& [1/2]Mutex(mutex);
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        println!("{}", *counter);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req Counter(counter, mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data);
    //@ close print_count_pre()(data);
    //@ print_count_Spawnee();
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
        //@ close Counter(counter, mutex);
        print_count_async(counter, mutex);
        loop {
            //@ inv true;
            let source = wait_for_source();
            //@ assume(false);
            count_pulses_async(counter, mutex, source);
        }
    }
}