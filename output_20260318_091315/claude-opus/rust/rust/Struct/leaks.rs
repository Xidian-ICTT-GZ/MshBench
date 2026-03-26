#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

predicate mutex(m: *mut Mutex;) = m-> ?mutex_val &*&
    mutex_val != 0; 

predicate mutex_guard(m: *mut Mutex;) = m-> ?mutex_val &*&
    mutex_val != 0; 

predicate counter(counter: *mut u32, v: u32) =
    counter |-> v;

predicate count_pulses_data(CountPulsesData data) =
    counter(data.counter, ?v) &*& mutex(data.mutex) &*&
    true;

predicate print_count_data(PrintCountData data) =
    counter(data.counter, ?v) &*& mutex(data.mutex);

predicate is_Spawnee(unsafe fn(arg: CountPulsesData), (CountPulsesData) -> bool pre) = true;
predicate is_Spawnee(unsafe fn(arg: PrintCountData), (PrintCountData) -> bool pre) = true;

predicate sendable<T>(Sendable<T> *s; T val) = s->payload |-> val;

unsafe fn spawn<T>(f: unsafe fn(arg: T), arg: T)
//@ requires [_]is_Spawnee(f, ?pre) &*& pre(arg) &*& sendable(&Sendable { payload: arg }, arg);
//@ ensures true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

unsafe fn create_mutex() -> *mut Mutex
//@ requires true;
//@ ensures mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex)
//@ requires mutex(mutex);
//@ ensures mutex(mutex) &*& mutex_guard(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ requires mutex_guard(?m);
//@ ensures mutex(m);
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ requires true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ requires true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
//@ requires true;
//@ ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ requires count_pulses_data(data);
//@ ensures count_pulses_data(data);
{
    let CountPulsesData {counter, mutex, source} = data;

    predicate loop_inv(bool done) =
        count_pulses_data(data);

    loop {
        fold loop_inv(false);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        open count_pulses_data(data);
        open counter(counter, ?v);
        *counter = v.checked_add(1).unwrap();
        close counter(counter, v + 1);
        close count_pulses_data(data);
        release(guard);
        fold loop_inv(false);
    }
    close count_pulses_data(data);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ requires counter(counter, ?v) &*& mutex(mutex);
//@ ensures true;
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ requires print_count_data(data);
//@ ensures print_count_data(data);
{
    let PrintCountData {counter, mutex} = data;

    predicate loop_inv() = print_count_data(data);

    loop {
        fold loop_inv();
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        open print_count_data(data);
        open counter(counter, ?v);
        print_u32(v);
        close counter(counter, v);
        close print_count_data(data);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ requires counter(counter, ?v) &*& mutex(mutex);
//@ ensures true;
{
    let data = PrintCountData { counter, mutex };
    spawn(print_count, data);
}

fn main()
//@ requires true;
//@ ensures true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);

        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}