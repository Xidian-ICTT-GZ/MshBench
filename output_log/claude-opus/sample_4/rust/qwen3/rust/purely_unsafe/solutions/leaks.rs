#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}

unsafe impl<T> Send for Sendable<T> {}

/*@

pred mutex_inv(counter: *mut u32;) = (*counter) |-> _;

pred mutex_held(mutex: *mut Mutex, frac: real;) = [frac](*mutex) |-> _;

pred counter_ptr(counter: *mut u32;) = true;

pred mutex_ptr(mutex: *mut Mutex;) = true;

pred count_pulses_data_pred(data: CountPulsesData;) =
    counter_ptr(data.counter) &*&
    mutex_ptr(data.mutex);

pred print_count_data_pred(data: PrintCountData;) =
    counter_ptr(data.counter) &*&
    mutex_ptr(data.mutex);

@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req true;
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
//@ ens (*result) |-> _;
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req (*mutex) |-> ?v;
//@ ens (*mutex) |-> v;
{
    let guard = (*mutex).lock().unwrap();
    guard
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
//@ req (*data.counter) |-> ?cnt_val &*& (*data.mutex) |-> ?mutex_val;
//@ ens (*data.counter) |-> _ &*& (*data.mutex) |-> mutex_val;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop
    //@ inv (*counter) |-> _ &*& (*mutex) |-> mutex_val;
    {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);
        let old_val = *counter;
        *counter = old_val.checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req (*counter) |-> ?cnt_val &*& (*mutex) |-> ?mutex_val;
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

unsafe fn print_count(data: PrintCountData)
//@ req (*data.counter) |-> ?cnt_val &*& (*data.mutex) |-> ?mutex_val;
//@ ens false;
{
    let PrintCountData { counter, mutex } = data;
    loop
    //@ inv (*counter) |-> _ &*& (*mutex) |-> mutex_val;
    {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        let val = *counter;
        print_u32(val);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req (*counter) |-> ?cnt_val &*& (*mutex) |-> ?mutex_val;
//@ ens true;
{
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens false;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);

        loop
        //@ inv true;
        {
            let source = wait_for_source();
            //@ assume(false);
            count_pulses_async(counter, mutex, source);
        }
    }
}