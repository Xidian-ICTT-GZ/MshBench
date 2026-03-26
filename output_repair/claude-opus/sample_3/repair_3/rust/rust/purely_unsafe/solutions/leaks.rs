#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@

pred counter_cell(p: *mut u32, v: u32) = *p |-> v;

pred mutex_alloc(m: *mut Mutex) = *m |-> _;

pred mutex_inv(m: *mut Mutex, p: *mut u32;) = mutex_alloc(m) &*& counter_cell(p, _);

pred count_pulses_pre(data: CountPulsesData) =
    mutex_inv(data.mutex, data.counter);

pred print_count_pre(data: PrintCountData) =
    mutex_inv(data.mutex, data.counter);

@*/

struct Sendable<T> {
    payload: T,
}
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

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_alloc(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    //@ close mutex_alloc(mutex);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_alloc(mutex);
//@ ens mutex_alloc(mutex);
{
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

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_pre(data);
//@ ens true;
{
    //@ open count_pulses_pre(data);
    //@ open mutex_inv(data.mutex, data.counter);
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        //@ inv mutex_alloc(mutex) &*& counter_cell(counter, _);
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);
        //@ open counter_cell(counter, _);

        *counter = (*counter).checked_add(1).unwrap();

        //@ close counter_cell(counter, _);
        release(guard);
    }
    //@ leak mutex_alloc(mutex);
    //@ leak counter_cell(counter, _);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [_]is_Spawnee(count_pulses, count_pulses_pre) &*& mutex_inv(mutex, counter);
//@ ens true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    //@ close count_pulses_pre(data);

    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req print_count_pre(data);
//@ ens true;
{
    //@ open print_count_pre(data);
    //@ open mutex_inv(data.mutex, data.counter);
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv mutex_alloc(mutex) &*& counter_cell(counter, _);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open counter_cell(counter, _);

        print_u32(*counter);

        //@ close counter_cell(counter, _);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req [_]is_Spawnee(print_count, print_count_pre) &*& mutex_inv(mutex, counter);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close print_count_pre(data);

    spawn(print_count, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close counter_cell(counter, 0);

        let mutex = create_mutex();
        //@ close mutex_inv(mutex, counter);

        //@ produce_fn_ptr_chunk is_Spawnee(print_count, print_count_pre)(data) { call(); }
        print_count_async(counter, mutex);

        loop {
            //@ inv true;
            let source = wait_for_source();
            //@ assume(false);
            count_pulses_async(counter, mutex, source);
        }
    }
}