#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

#[pred]
fn mutex_inner(mutex_ptr: *mut Mutex, inv: pred) = mutex_ptr |-> _mutex_instance &*& inv;

#[pred_def]
fn mutex_pred(mutex: *mut Mutex, inv: pred) : 
  mutex_inner(mutex, inv)
{
    // Ownership of the Mutex instance on the heap and the invariant
}

#[pred_def]
fn counter_pred(counter: *mut u32, val: i32) =
  counter |-> val
;

#[pred_def]
fn count_pulses_data_pred(data: CountPulsesData, cnt_val: i32) =
  counter_pred(data.counter, cnt_val) &*&
  mutex_pred(data.mutex, true)
;

#[pred_def]
fn print_count_data_pred(data: PrintCountData, cnt_val: i32) =
  counter_pred(data.counter, cnt_val) &*&
  mutex_pred(data.mutex, true)
;

#[pred_def]
fn spawnee_pred<T>(f: unsafe fn(arg: T), pre: pred) =
  exists?(arg: T) { pre }
;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
  //@ requires [_]spawnee_pred(f, ?pre) &*& pre(arg);
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

unsafe fn create_mutex()
  //@ requires true;
  //@ ensures mutex_pred(result, true);
{
    //@ open malloc_layout(Layout::new::<Mutex>());
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    //@ close mutex_pred(mutex, true);
    //@ leak mutex_pred(mutex, true);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex)
  //@ requires mutex_pred(mutex, ?inv);
  //@ ensures mutex_pred(mutex, inv) &*& result == _;
{
    //@ open mutex_pred(mutex, inv);
    let guard = (*mutex).lock().unwrap();
    //@ close mutex_pred(mutex, inv);
    guard
}

unsafe fn release(guard: MutexGuard)
  //@ requires mutex_pred(?mutex, ?inv);
  //@ ensures mutex_pred(mutex, inv);
{
    //@ open mutex_pred(mutex, inv);
    drop(guard);
    //@ close mutex_pred(mutex, inv);
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
  //@ requires count_pulses_data_pred(data, ?cnt);
  //@ ensures count_pulses_data_pred(data, cnt);
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    //@ open count_pulses_data_pred(data, ?cnt);
    loop
        //@ invariant count_pulses_data_pred(data, ?loop_cnt);
        //@ decreases _;
    {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        //@ open count_pulses_data_pred(data, ?loop_cnt);
        let guard = acquire(mutex);
        //@ open mutex_pred(mutex, true);
        //@ assert counter |-> ?old_cnt;
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_pred(counter, old_cnt + 1);
        //@ close mutex_pred(mutex, true);
        release(guard);
        //@ close count_pulses_data_pred(data, loop_cnt + 1);
    }
    //@ close count_pulses_data_pred(data, cnt);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
  //@ requires counter_pred(counter, ?cnt) &*& mutex_pred(mutex, true);
  //@ ensures true;
{
    //@ open counter_pred(counter, ?cnt);
    //@ open mutex_pred(mutex, true);
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
    //@ open print_count_data_pred(data, ?cnt);
    loop
      //@ invariant print_count_data_pred(data, ?loop_cnt);
      //@ decreases _;
    {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        //@ open print_count_data_pred(data, ?loop_cnt);
        let guard = acquire(mutex);
        //@ open mutex_pred(mutex, true);
        //@ assert counter |-> ?val;
        print_u32(*counter);
        //@ close counter_pred(counter, val);
        //@ close mutex_pred(mutex, true);
        release(guard);
        //@ close print_count_data_pred(data, loop_cnt);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
  //@ requires counter_pred(counter, ?cnt) &*& mutex_pred(mutex, true);
  //@ ensures true;
{
    //@ open counter_pred(counter, ?cnt);
    //@ open mutex_pred(mutex, true);
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