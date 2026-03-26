#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
pred counter_own(counter: *mut u32;) = counter |-> _;

pred mutex_own(mutex: *mut Mutex;) = mutex |-> _;

pred count_pulses_data_own(data: CountPulsesData;) = 
  counter_own(data.counter) &*& mutex_own(data.mutex);

pred print_count_data_own(data: PrintCountData;) = 
  counter_own(data.counter) &*& mutex_own(data.mutex);
@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req true;
//@ ens true;
{
    let package = Sendable { payload: arg };
    let _f = f;
    let _package = package;
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
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
//@ req mutex_own(mutex);
//@ ens mutex_own(mutex);
{
    (&*mutex).lock().unwrap()
}

unsafe fn release(_guard: MutexGuard)
//@ req true;
//@ ens true;
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
//@ req count_pulses_data_own(data);
//@ ens true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    loop {
        //@ inv counter_own(counter) &*& mutex_own(mutex);
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
//@ req counter_own(counter) &*& mutex_own(mutex);
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
//@ req print_count_data_own(data);
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv counter_own(counter) &*& mutex_own(mutex);
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
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