#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

#[pred]
struct MutexPred<'a>(MutexGuard<'a>);

#[pred]
struct CountPulsesDataPred {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
} = 
    counter_owned(counter) &*& 
    mutex_owned(mutex);

#[pred]
struct PrintCountDataPred {
    counter: *mut u32,
    mutex: *mut Mutex,
} = 
    counter_owned(counter) &*&
    mutex_owned(mutex);

#[pred]
struct SendablePred<T> {
    payload: T,
} = true; // used as marker, see below for heap ownership in lemmas

#[predicate]
fn counter_owned(counter: *mut u32) = 
    counter != std::ptr::null_mut() &*& 
    counter_cell(counter, ?v);

predicate counter_cell(counter: *mut u32, v: u32) = counter->v;

#[predicate]
fn mutex_owned(mutex: *mut Mutex) = 
    mutex != std::ptr::null_mut() &*& 
    mutex_cell(mutex);

predicate mutex_cell(mutex: *mut Mutex) = mutex->_;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[lemma]
fn sendable_send<T>() -> ()
    requires
        exists(|t: T| SendablePred { payload: t } &*& owns_sendable_payload(t))
    ensures
        exists(|t: T| SendablePred { payload: t } &*& owns_sendable_payload(t));
{}

predicate owns_sendable_payload<T>(payload: T) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
where
    T: Copy,
{
    #[requires(exists::<T>(|x| SendablePred { payload: x } &*& owns_sendable_payload(x)) &*& SendablePred { payload: arg } &*& owns_sendable_payload(arg))]
    #[ensures(exists::<T>(|x| SendablePred { payload: x } &*& owns_sendable_payload(x)))]
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
    #[ensures(MutexPred(result) &*& mutex_owned(mutex))]
    (&*mutex).lock().unwrap()
}

unsafe fn release(_guard: MutexGuard) {
    #[requires(MutexPred(_guard))]
    #[ensures(emp)]
    {}
}

unsafe fn wait_for_pulse(_source: i32) -> bool {
    #[requires(emp)]
    #[ensures(true)]
    true
}

unsafe fn wait_for_source() -> i32 {
    #[requires(emp)]
    #[ensures(true)]
    1
}

unsafe fn count_pulses(data: CountPulsesData) {
    #[requires(CountPulsesDataPred { counter: data.counter, mutex: data.mutex, source: data.source })]
    #[ensures(CountPulsesDataPred { counter: data.counter, mutex: data.mutex, source: data.source })]
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    #[invariant(CountPulsesDataPred { counter: counter, mutex: mutex, source: source })]
    loop {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);
        #[requires(counter_owned(counter) &*& MutexPred(guard))]
        #[ensures(counter_owned(counter) &*& MutexPred(guard))]
        {
            // Open and update the counter cell
            open counter_owned(counter);
            open counter_cell(counter, ?old_val);
            *counter = old_val.checked_add(1).unwrap();
            close counter_cell(counter, old_val + 1);
            close counter_owned(counter);
        }
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    #[requires(counter_owned(counter) &*& mutex_owned(mutex))]
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
    #[requires(PrintCountDataPred { counter: data.counter, mutex: data.mutex })]
    #[ensures(PrintCountDataPred { counter: data.counter, mutex: data.mutex })]
    let PrintCountData { counter, mutex } = data;
    #[invariant(PrintCountDataPred { counter: counter, mutex: mutex })]
    loop {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        #[requires(counter_owned(counter) &*& MutexPred(guard))]
        #[ensures(counter_owned(counter) &*& MutexPred(guard))]
        {
            open counter_owned(counter);
            open counter_cell(counter, ?val);
            // printing does not mutate counter
            close counter_cell(counter, val);
            close counter_owned(counter);
            println!("{}", val);
        }
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex) {
    #[requires(counter_owned(counter) &*& mutex_owned(mutex))]
    #[ensures(true)]
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main() {
    unsafe {
        #[requires(emp)]
        #[ensures(counter_owned(result))]
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        #[requires(counter_owned(counter))]
        #[ensures(counter_owned(counter))]
        {
            open counter_owned(counter);
            open counter_cell(counter, ?_);
            *counter = 0;
            close counter_cell(counter, 0);
            close counter_owned(counter);
        }

        let mutex = create_mutex();

        print_count_async(counter, mutex);
        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}