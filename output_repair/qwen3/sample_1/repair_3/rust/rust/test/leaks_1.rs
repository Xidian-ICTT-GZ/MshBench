#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
pred Mutex_own(mutex: *mut Mutex;);

pred_ctor counter_inv(counter: *mut u32)() = (*counter) |-> _;

pred Mutex_locked(mutex: *mut Mutex, counter: *mut u32; guard: MutexGuard) =
    Mutex_own(mutex) &*& (*counter) |-> _;

pred CountPulsesData_own(data: CountPulsesData; counter: *mut u32, mutex: *mut Mutex, source: i32) =
    data.counter |-> counter &*& data.mutex |-> mutex &*& data.source |-> source;

pred PrintCountData_own(data: PrintCountData; counter: *mut u32, mutex: *mut Mutex) =
    data.counter |-> counter &*& data.mutex |-> mutex;

pred thread_token(counter: *mut u32, mutex: *mut Mutex) = true;
@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req true;
//@ ens true;
{
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

/*@
pred alloc_block_u32(p: *mut u32;) = (*p) |-> _;
pred alloc_block_Mutex(p: *mut Mutex;) = Mutex_own(p);
@*/

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens Mutex_own(result);
{
    let layout = Layout::new::<Mutex>();
    let mutex = alloc(layout) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(layout);
    }
    mutex.write(Mutex::new(()));
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req Mutex_own(mutex);
//@ ens Mutex_locked(mutex, ?counter, result) &*& (*counter) |-> _;
{
    (&*mutex).lock().unwrap()
}

unsafe fn release(_guard: MutexGuard)
//@ req Mutex_locked(?mutex, ?counter, _guard) &*& (*counter) |-> _;
//@ ens Mutex_own(mutex) &*& (*counter) |-> _;
{
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{
    true
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{
    1
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data, ?counter, ?mutex, ?source) &*& Mutex_own(mutex) &*& (*counter) |-> _;
//@ ens true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    loop {
        //@ inv Mutex_own(mutex) &*& (*counter) |-> _;
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
//@ req Mutex_own(mutex) &*& (*counter) |-> _;
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
//@ req PrintCountData_own(data, ?counter, ?mutex) &*& Mutex_own(mutex) &*& (*counter) |-> _;
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv Mutex_own(mutex) &*& (*counter) |-> _;
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);

        println!("{}", *counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req Mutex_own(mutex) &*& (*counter) |-> _;
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
        let layout = Layout::new::<u32>();
        let counter = alloc(layout) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(layout);
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