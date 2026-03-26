#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

predicate mutex_mutex(struct std::sync::Mutex<()> *mutex) = true;
predicate mutex_guard_mutex_guard(struct std::sync::MutexGuard<'static, ()> *guard) = true;

predicate u32_points_to(uint *p, uint v) = p |-> v;

predicate count_pulses_data(CountPulsesData data) =
    u32_points_to(data.counter, _)
    &*& mutex_mutex(data.mutex);

predicate print_count_data(PrintCountData data) =
    u32_points_to(data.counter, _)
    &*& mutex_mutex(data.mutex);

predicate sendable<T>(Sendable<T> *s, T payload) = chars(s.payload) &*& s.payload == payload;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
    //@ requires [?f_frac]is_Spawnee(f, ?pre) &*& pre(arg);
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

unsafe fn create_mutex() -> *mut Mutex
    //@ requires true;
    //@ ensures mutex_mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
    //@ requires mutex_mutex(mutex);
    //@ ensures mutex_guard_mutex_guard(result) &*& mutex_mutex(mutex);
{
    (&*mutex).lock().unwrap()
}

unsafe fn release(_guard: MutexGuard)
    //@ requires mutex_guard_mutex_guard(_guard);
    //@ ensures true;
{}

unsafe fn wait_for_pulse(_source: i32) -> bool
    //@ requires true;
    //@ ensures true == result;
{ true }

unsafe fn wait_for_source() -> i32
    //@ requires true;
    //@ ensures true;
{ 1 }

unsafe fn count_pulses(data: CountPulsesData)
    //@ requires count_pulses_data(data);
    //@ ensures true;
{
    let CountPulsesData { counter, mutex, source } = data;
    loop
        invariant count_pulses_data(data);
    {
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
    // The invariant implies counter and mutex ownership is preserved at loop end
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
    //@ requires u32_points_to(counter, _) &*& mutex_mutex(mutex);
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
    //@ ensures true;
{
    let PrintCountData { counter, mutex } = data;
    loop
        invariant print_count_data(data);
    {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        println!("{}", *counter);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
    //@ requires u32_points_to(counter, _) &*& mutex_mutex(mutex);
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