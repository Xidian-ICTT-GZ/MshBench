#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

predicate mutex(m: *mut Mutex) = m->field();
predicate u32_box(p: *mut u32, v: u32) = p |-> v;

predicate count_pulses_data(CountPulsesData data) = 
    u32_box(data.counter, _) &*& mutex(data.mutex) &*& true;

predicate print_count_data(PrintCountData data) = 
    u32_box(data.counter, _) &*& mutex(data.mutex);

predicate is_Spawnee(unsafe fn(arg: CountPulsesData), predicate<CountPulsesData> pre) = pre;

predicate is_Spawnee_print(unsafe fn(arg: PrintCountData), predicate<PrintCountData> pre) = pre;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ requires [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ensures true;
{
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[predicate]
fn field() = true; 

unsafe fn create_mutex() -> *mut Mutex
//@ requires true;
//@ ensures mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    assume(mutex != core::ptr::null_mut());
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ requires mutex(mutex);
//@ ensures mutex(mutex);
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ requires mutex(_);
//@ ensures mutex(_);
{}

unsafe fn wait_for_pulse(_source: i32) -> bool 
//@ requires true;
//@ ensures true;
{ true }
unsafe fn wait_for_source() -> i32 
//@ requires true;
//@ ensures true;
{ 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ requires count_pulses_data(data);
//@ ensures count_pulses_data(data);
{
    let CountPulsesData { counter, mutex, source } = data;
    predicate_loop_invariant(counter: *mut u32, mutex: *mut Mutex) = 
      u32_box(counter, _) &*& mutex(mutex);

    loop invariant predicate_loop_invariant(counter, mutex);
    {
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        u32_box(counter, ?v);
        u32_box(counter, v + 1);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ requires u32_box(counter, ?) &*& mutex(mutex);
//@ ensures true;
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

unsafe fn print_count(data: PrintCountData)
//@ requires print_count_data(data);
//@ ensures print_count_data(data);
{
    let PrintCountData { counter, mutex } = data;
    predicate_loop_invariant(counter: *mut u32, mutex: *mut Mutex) = 
      u32_box(counter, _) &*& mutex(mutex);

    loop invariant predicate_loop_invariant(counter, mutex);
    {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        u32_box(counter, ?v);
        println!("{}", *counter);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ requires u32_box(counter, ?) &*& mutex(mutex);
//@ ensures true;
{
    let data = PrintCountData { counter, mutex };
    spawn(print_count, data);
}

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);
        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}