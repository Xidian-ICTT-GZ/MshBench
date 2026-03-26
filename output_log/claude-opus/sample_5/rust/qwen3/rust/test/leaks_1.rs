#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

#[pred]
struct MutexPred<'a>(MutexGuard<'a>)
    = mutex_guard(&self.0);

#[predicate]
fn mutex_guard(_g: &MutexGuard) = emp; 

#[pred]
struct CountPulsesDataPred {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
} = count_pulses_data_owned(CountPulsesData { counter, mutex, source });

#[pred]
struct PrintCountDataPred {
    counter: *mut u32,
    mutex: *mut Mutex,
} = print_count_data_owned(PrintCountData { counter, mutex });

#[pred]
struct SendablePred<T> {
    payload: T,
} = sendable_pred(payload);

#[predicate]
fn sendable_pred<T>(payload: T) = emp; // Just a marker predicate; actual ownership is explained below

#[lemma]
fn sendable_send<T>() -> ()
    requires exists::<T>(|t| sendable_pred(t));
    ensures  exists::<T>(|t| sendable_pred(t));
{
}

#[predicate]
fn allocated<T>(p: *mut T) = p != std::ptr::null_mut() &*& malloc_block::<T>(p);

#[predicate]
fn u32_owned(p: *mut u32) = allocated(p) &*& *p |-> ?v;

#[predicate]
fn mutex_owned(p: *mut Mutex) = allocated(p) &*& mutex_invariant(p);

#[predicate]
fn mutex_invariant(p: *mut Mutex) = true; // internal mutex state

#[predicate]
fn count_pulses_data_owned(data: CountPulsesData) =
    u32_owned(data.counter) &*& mutex_owned(data.mutex) &*& true;

#[predicate]
fn print_count_data_owned(data: PrintCountData) =
    u32_owned(data.counter) &*& mutex_owned(data.mutex) &*& true;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
where
    T: Copy,
{
    #[requires(exists::<T>(|x| sendable_pred(x)) &*& sendable_pred(arg))]
    #[ensures(exists::<T>(|x| sendable_pred(x)))]
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
        #[requires(u32_owned(counter) &*& MutexPred(guard))]
        #[ensures(u32_owned(counter) &*& MutexPred(guard))]
        {
            *counter = (*counter).checked_add(1).unwrap();
        }
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    #[requires(u32_owned(counter) &*& mutex_owned(mutex))]
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
    #[requires(print_count_data_owned(data))]
    #[ensures(print_count_data_owned(data))]
    let PrintCountData { counter, mutex } = data;

    #[invariant(print_count_data_owned(data))]
    loop {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        #[requires(u32_owned(counter) &*& MutexPred(guard))]
        #[ensures(u32_owned(counter) &*& MutexPred(guard))]
        {
            println!("{}", *counter);
        }
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex) {
    #[requires(u32_owned(counter) &*& mutex_owned(mutex))]
    #[ensures(true)]
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