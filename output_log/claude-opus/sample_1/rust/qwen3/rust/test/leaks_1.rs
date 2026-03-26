#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

#[pred]
struct MutexPred<'a>(MutexGuard<'a>)
    = emp; // Ownership of the MutexGuard tied to the lock guard, no internal fields exposed here

#[pred]
struct CountPulsesDataPred {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}
#[predicate]
fn count_pulses_data_owned(data: CountPulsesData) =
    u32_owned(data.counter) &* mutex_owned(data.mutex);

#[pred]
struct PrintCountDataPred {
    counter: *mut u32,
    mutex: *mut Mutex,
}
#[predicate]
fn print_count_data_owned(data: PrintCountData) =
    u32_owned(data.counter) &* mutex_owned(data.mutex);

#[pred]
struct SendablePred<T> {
    payload: T,
}

#[lemma]
fn sendable_send<T>() -> ()
  requires exists(|t: T| SendablePred { payload: t })
  ensures exists(|t: T| SendablePred { payload: t })
{
  // noop lemma for sendable predicate preservation
}

#[predicate]
fn allocated<T>(p: *mut T) =
    p != std::ptr::null_mut() &* emp;

#[predicate]
fn u32_owned(p: *mut u32) =
    p != std::ptr::null_mut() &* p |-> _;

#[predicate]
fn mutex_owned(p: *mut Mutex) =
    p != std::ptr::null_mut() &* p |-> _;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
where
    T: Copy,
{
    #[requires(exists::<T>(|x| SendablePred { payload: x }) && SendablePred { payload: arg })]
    #[ensures(exists::<T>(|x| SendablePred { payload: x }))]
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex {
    #[requires(emp)]
    #[ensures(mutex_owned(result))]
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    #[requires(mutex_owned(mutex))]
    #[ensures(mutex_owned(mutex))]
    mutex.write(Mutex::new(()));
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    #[requires(mutex_owned(mutex))]
    #[ensures(MutexPred(result))]
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard) {
    #[requires(MutexPred(_guard))]
    #[ensures(emp)]
    {}
}

unsafe fn wait_for_pulse(_source: i32) -> bool {
    #[requires(emp)]
    #[ensures(emp)]
    true
}
unsafe fn wait_for_source() -> i32 {
    #[requires(emp)]
    #[ensures(emp)]
    1
}

unsafe fn count_pulses(data: CountPulsesData) {
    #[requires(count_pulses_data_owned(data))]
    #[ensures(count_pulses_data_owned(data))]
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    #[invariant(count_pulses_data_owned(data))]
    loop {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);

        #[requires(u32_owned(counter) &* MutexPred(guard))]
        #[ensures(u32_owned(counter) &* MutexPred(guard))]
        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    #[requires(u32_owned(counter) &* mutex_owned(mutex))]
    #[ensures(emp)]
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
    #[requires(print_count_data_owned(data))]
    #[ensures(print_count_data_owned(data))]
    let PrintCountData { counter, mutex } = data;
    #[invariant(print_count_data_owned(data))]
    loop {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);

        #[requires(u32_owned(counter) &* MutexPred(guard))]
        #[ensures(u32_owned(counter) &* MutexPred(guard))]
        println!("{}", *counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex) {
    #[requires(u32_owned(counter) &* mutex_owned(mutex))]
    #[ensures(emp)]
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main() {
    unsafe {
        #[requires(emp)]
        #[ensures(u32_owned(result))]
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        #[requires(u32_owned(counter))]
        #[ensures(u32_owned(counter))]
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);
        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}