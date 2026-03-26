#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

predicate_ctor is_Spawnee<T>(f: unsafe fn(arg: T))(arg: T) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
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

predicate mutex_pointer(m: *mut Mutex) = 
    struct_Mutex_padding(m) &*& (*m).data |-> ?inner &*& (*m).poison |-> ?poison &*& inner == () &*& poison == false;

predicate mutex_guard(g: MutexGuard) = 
    mutex_guard_data(g, ?m) &*& mutex_pointer(m);

unsafe fn create_mutex() -> *mut Mutex 
//@ req true;
//@ ens mutex_pointer(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard 
//@ req mutex_pointer(mutex);
//@ ens mutex_guard(result);
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

predicate count_pulses_data(data: CountPulsesData) = 
    data.counter |-> ?counter &*& integer(counter, ?count) &*& 
    data.mutex |-> ?mutex &*& mutex_pointer(mutex) &*& 
    data.source |-> ?source &*& source is i32;

unsafe fn count_pulses(data: CountPulsesData) 
//@ req count_pulses_data(data);
//@ ens true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop 
    //@ inv integer(counter, ?count) &*& mutex_pointer(mutex) &*& source is i32;
    {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) 
//@ req integer(counter, ?count) &*& mutex_pointer(mutex) &*& source is i32;
//@ ens true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

predicate print_count_data(data: PrintCountData) = 
    data.counter |-> ?counter &*& integer(counter, ?count) &*& 
    data.mutex |-> ?mutex &*& mutex_pointer(mutex);

unsafe fn print_count(data: PrintCountData) 
//@ req print_count_data(data);
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    loop 
    //@ inv integer(counter, ?count) &*& mutex_pointer(mutex);
    {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        print_u32(*counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex) 
//@ req integer(counter, ?count) &*& mutex_pointer(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);

        loop 
        //@ inv integer(counter, ?count) &*& mutex_pointer(mutex);
        {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}