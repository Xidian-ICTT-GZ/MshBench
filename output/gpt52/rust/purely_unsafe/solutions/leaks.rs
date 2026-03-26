#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

//@ predicate counter_ptr(p: *mut u32; v: u32) = p as usize != 0 &*& *p |-> v;

//@ predicate mutex_ptr(p: *mut Mutex) = p as usize != 0 &*& std::sync::Mutex(p, ());
//@ predicate mutex_guard(g: MutexGuard, p: *mut Mutex) = std::sync::MutexGuard(g, p);

//@ predicate shared_counter_mutex(counter: *mut u32, mutex: *mut Mutex) = counter_ptr(counter, ?v) &*& mutex_ptr(mutex);

//@ predicate_ctor counter_mutex_inv(counter: *mut u32, mutex: *mut Mutex)() = shared_counter_mutex(counter, mutex);

//@ predicate is_Spawnee<T>(f: unsafe fn(arg: T), pre: pred(T)) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req is_Spawnee(f, ?pre) &*& pre(arg);
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
//@ ens mutex_ptr(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_ptr(mutex);
//@ ens mutex_guard(result, mutex) &*& mutex_ptr(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(guard, ?mutex) &*& mutex_ptr(mutex);
//@ ens mutex_ptr(mutex);
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
//@ req shared_counter_mutex(data.counter, data.mutex);
//@ ens shared_counter_mutex(data.counter, data.mutex);
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        //@ invariant shared_counter_mutex(counter, mutex);
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);

        //@ open shared_counter_mutex(counter, mutex);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close shared_counter_mutex(counter, mutex);

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req shared_counter_mutex(counter, mutex);
//@ ens shared_counter_mutex(counter, mutex);
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    //@ produce_fn_ptr_chunk is_Spawnee(count_pulses)(shared_counter_mutex(counter, mutex))() { }
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req shared_counter_mutex(data.counter, data.mutex);
//@ ens shared_counter_mutex(data.counter, data.mutex);
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ invariant shared_counter_mutex(counter, mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        //@ open shared_counter_mutex(counter, mutex);
        print_u32(*counter);
        //@ close shared_counter_mutex(counter, mutex);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req shared_counter_mutex(counter, mutex);
//@ ens shared_counter_mutex(counter, mutex);
{
    let data = PrintCountData { counter, mutex };

    //@ produce_fn_ptr_chunk is_Spawnee(print_count)(shared_counter_mutex(counter, mutex))() { }
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
        //@ close counter_ptr(counter, 0);
        *counter = 0;

        let mutex = create_mutex();

        //@ close shared_counter_mutex(counter, mutex);
        print_count_async(counter, mutex);
        //@ open shared_counter_mutex(counter, mutex);
        //@ close shared_counter_mutex(counter, mutex);

        loop {
            //@ invariant shared_counter_mutex(counter, mutex);
            let source = wait_for_source();
            //@ open shared_counter_mutex(counter, mutex);
            //@ close shared_counter_mutex(counter, mutex);
            count_pulses_async(counter, mutex, source);
            //@ open shared_counter_mutex(counter, mutex);
            //@ close shared_counter_mutex(counter, mutex);
        }
    }
}