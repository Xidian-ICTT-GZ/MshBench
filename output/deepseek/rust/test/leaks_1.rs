#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn sendable<T>(s: &Sendable<T>) -> bool { true }

#[predicate]
fn mutex_points_to(m: *mut Mutex, frac: rational, inner: *const ()) -> bool { 
    m != std::ptr::null_mut() && 
    exists(|inner_ptr: *const ()| inner_ptr == inner)
}

#[predicate]
fn mutex_guard_points_to(g: &MutexGuard, inner: *const ()) -> bool { 
    exists(|inner_ptr: *const ()| inner_ptr == inner)
}

#[predicate]
fn u32_points_to(p: *mut u32, v: u32) -> bool { 
    p != std::ptr::null_mut()
}

#[predicate]
fn count_pulses_data_points_to(d: &CountPulsesData, counter: *mut u32, mutex: *mut Mutex, source: i32) -> bool {
    d.counter == counter && d.mutex == mutex && d.source == source
}

#[predicate]
fn print_count_data_points_to(d: &PrintCountData, counter: *mut u32, mutex: *mut Mutex) -> bool {
    d.counter == counter && d.mutex == mutex
}

#[predicate]
fn full_mutex(m: *mut Mutex) -> bool {
    mutex_points_to(m, 1, std::ptr::null())
}

#[predicate]
fn counter_owned(c: *mut u32, v: u32) -> bool {
    u32_points_to(c, v)
}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    #[requires(sendable(&Sendable { payload: arg }))]
    #[ensures(true)]
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex {
    #[requires(true)]
    #[ensures(full_mutex(result))]
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

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    #[requires(full_mutex(mutex))]
    #[ensures(|guard| mutex_guard_points_to(guard, std::ptr::null()))]
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard) {
    #[requires(|guard| mutex_guard_points_to(guard, std::ptr::null()))]
    #[ensures(true)]
}

unsafe fn wait_for_pulse(_source: i32) -> bool {
    #[requires(true)]
    #[ensures(true)]
    true
}
unsafe fn wait_for_source() -> i32 {
    #[requires(true)]
    #[ensures(true)]
    1
}

unsafe fn count_pulses(data: CountPulsesData) {
    #[requires(count_pulses_data_points_to(&data, data.counter, data.mutex, data.source) && 
        counter_owned(data.counter, ?v) && full_mutex(data.mutex))]
    #[ensures(true)]
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    loop {
        #[invariant(counter_owned(counter, ?cur_val) && full_mutex(mutex))]
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    #[requires(counter_owned(counter, ?v) && full_mutex(mutex))]
    #[ensures(true)]
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

unsafe fn print_count(data: PrintCountData) {
    #[requires(print_count_data_points_to(&data, data.counter, data.mutex) && 
        counter_owned(data.counter, ?v) && full_mutex(data.mutex))]
    #[ensures(true)]
    let PrintCountData { counter, mutex } = data;
    loop {
        #[invariant(counter_owned(counter, ?cur_val) && full_mutex(mutex))]
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);

        println!("{}", *counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex) {
    #[requires(counter_owned(counter, ?v) && full_mutex(mutex))]
    #[ensures(true)]
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main() {
    unsafe {
        #[requires(true)]
        #[ensures(counter_owned(?counter, 0) && full_mutex(?mutex))]
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);
        loop {
            #[invariant(counter_owned(counter, ?cur_val) && full_mutex(mutex))]
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}