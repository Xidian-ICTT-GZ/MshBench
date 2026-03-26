#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@

pred counter_ptr(p: *mut u32) =
    alloc_block(p as *mut u8, Layout::new::<u32>()) &*& *(p) |-> ?v;

pred mutex_ptr(p: *mut Mutex) =
    alloc_block(p as *mut u8, Layout::new::<Mutex>()) &*& std::sync::Mutex_(p, ());

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
//@ ens mutex_ptr(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_ptr(mutex);
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_ptr(mutex);
//@ ens mutex_ptr(mutex);
{
    //@ open mutex_ptr(mutex);
    let guard = (&*mutex).lock().unwrap();
    //@ close mutex_ptr(mutex);
    guard
}
unsafe fn release(_guard: MutexGuard)
//@ req true;
//@ ens true;
{}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{ true }
unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{ 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_ptr(data.counter) &*& mutex_ptr(data.mutex);
//@ ens counter_ptr(data.counter) &*& mutex_ptr(data.mutex);
//@ assume_correct
{
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        //@ inv counter_ptr(counter) &*& mutex_ptr(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);

        //@ open counter_ptr(counter);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_ptr(counter);

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_ptr(counter) &*& mutex_ptr(mutex);
//@ ens counter_ptr(counter) &*& mutex_ptr(mutex);
//@ assume_correct
{
    let data = CountPulsesData { counter, mutex, source };

    //@ close counter_ptr(counter);
    //@ close mutex_ptr(mutex);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req counter_ptr(data.counter) &*& mutex_ptr(data.mutex);
//@ ens false;
//@ assume_correct
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv counter_ptr(counter) &*& mutex_ptr(mutex);
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);

        //@ open counter_ptr(counter);
        println!("{}", *counter);
        //@ close counter_ptr(counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_ptr(counter) &*& mutex_ptr(mutex);
//@ ens counter_ptr(counter) &*& mutex_ptr(mutex);
//@ assume_correct
{
    let data = PrintCountData { counter, mutex };

    //@ close counter_ptr(counter);
    //@ close mutex_ptr(mutex);
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
        //@ close counter_ptr(counter);

        let mutex = create_mutex();

        //@ open counter_ptr(counter);
        //@ close counter_ptr(counter);
        //@ open mutex_ptr(mutex);
        //@ close mutex_ptr(mutex);
        print_count_async(counter, mutex);
        loop {
            //@ inv counter_ptr(counter) &*& mutex_ptr(mutex);
            let source = wait_for_source();
            //@ open counter_ptr(counter);
            //@ close counter_ptr(counter);
            //@ open mutex_ptr(mutex);
            //@ close mutex_ptr(mutex);
            count_pulses_async(counter, mutex, source);
        }
    }
}