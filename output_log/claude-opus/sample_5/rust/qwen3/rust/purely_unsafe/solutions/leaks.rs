#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

#[pred_def]
fn mutex_pred(mutex: *mut Mutex, inv: pred) -> pred {
    mutex |-> ?m &*& inv &*& m == ()
}

#[pred_def]
fn counter_pred(counter: *mut u32, val: i32) -> pred {
    counter |-> val
}

#[pred_def]
fn count_pulses_data_pred(data: CountPulsesData, cnt_val: i32) -> pred {
    data.counter |-> cnt_val &*&
    mutex_pred(data.mutex, true)
}

#[pred_def]
fn print_count_data_pred(data: PrintCountData, cnt_val: i32) -> pred {
    data.counter |-> cnt_val &*&
    mutex_pred(data.mutex, true)
}

#[pred]
fn spawnee_pred<T>(f: unsafe fn(arg: T), pre: (T) -> pred) = 
    exists?(arg: T) { pre(arg) };

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
    //@ requires spawnee_pred(f, ?pre) &*& pre(arg);
    //@ ensures true;
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
    //@ requires malloc_layout(Layout::new::<Mutex>());
    //@ ensures mutex_pred(result, true);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
    //@ requires mutex_pred(mutex, ?inv);
    //@ ensures mutex_pred(mutex, inv);
{
    let guard = (*mutex).lock().unwrap();
    guard
}

unsafe fn release(guard: MutexGuard)
    //@ requires mutex_pred(?mutex, ?inv);
    //@ ensures mutex_pred(mutex, inv);
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
    //@ requires emp;
    //@ ensures emp;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
    //@ requires emp;
    //@ ensures emp;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
    //@ requires emp;
    //@ ensures emp;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
    //@ requires count_pulses_data_pred(data, ?cnt);
    //@ ensures count_pulses_data_pred(data, cnt);
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    let mut count = cnt;
    loop
        //@ requires count_pulses_data_pred(data, count);
        //@ ensures count_pulses_data_pred(data, count);
    {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);
        // Open mutex predicate with inv == true
        //@ open mutex_pred(mutex, true);
        //@ assert counter |-> ?old_cnt;
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_pred(counter, old_cnt + 1);
        //@ close mutex_pred(mutex, true);
        release(guard);
        count = count + 1;
        //@ close count_pulses_data_pred(data, count);
    }
    //@ close count_pulses_data_pred(data, count);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
    //@ requires counter_pred(counter, ?cnt) &*& mutex_pred(mutex, true);
    //@ ensures true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    //@ close count_pulses_data_pred(data, cnt);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
    //@ requires print_count_data_pred(data, ?cnt);
    //@ ensures print_count_data_pred(data, cnt);
{
    let PrintCountData { counter, mutex } = data;

    let mut count = cnt;
    loop
        //@ requires print_count_data_pred(data, count);
        //@ ensures print_count_data_pred(data, count);
    {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex_pred(mutex, true);
        //@ assert counter |-> ?val;
        print_u32(*counter);
        //@ close counter_pred(counter, val);
        //@ close mutex_pred(mutex, true);
        release(guard);
        //@ close print_count_data_pred(data, count);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
    //@ requires counter_pred(counter, ?cnt) &*& mutex_pred(mutex, true);
    //@ ensures true;
{
    let data = PrintCountData { counter, mutex };

    //@ close print_count_data_pred(data, cnt);
    spawn(print_count, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        //@ open malloc_layout(Layout::new::<u32>());
        *counter = 0;
        //@ close counter_pred(counter, 0);

        let mutex = create_mutex();
        //@ close mutex_pred(mutex, true);

        print_count_async(counter, mutex);

        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}

#[predicate]
fn malloc_layout(layout: Layout) = true;

struct Sendable<T> { payload: T }