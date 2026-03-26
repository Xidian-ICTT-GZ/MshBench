#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

predicate u32_own(ptr: *mut u32, v: int) = ptr |-> v;

predicate struct_Mutex_padding(mutex: *mut Mutex) = mutex |-> _;

predicate mutex_own(mutex: *mut Mutex) = struct_Mutex_padding(mutex);

predicate counter_protected(counter: *mut u32, mutex: *mut Mutex) =
    u32_own(counter, _) &*& mutex_own(mutex);

predicate thread_token(counter: *mut u32, mutex: *mut Mutex) =
    [1/2]u32_own(counter, _) &*& [1/2]mutex_own(mutex);

predicate count_pulses_data_own(data: CountPulsesData) =
    data.counter |-> ?counter &*& data.mutex |-> ?mutex &*& data.source |-> _ &*&
    thread_token(counter, mutex);

predicate print_count_data_own(data: PrintCountData) =
    data.counter |-> ?counter &*& data.mutex |-> ?mutex &*&
    thread_token(counter, mutex);

#[requires(count_pulses_data_own(arg))]
#[ensures(true)]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[ensures(mutex_own(result) &*& u32_own(result as *mut u32, 0))]
unsafe fn create_mutex() -> *mut Mutex {
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

#[requires([1/2]u32_own(mutex as *mut u32, ?v) &*& [1/2]mutex_own(mutex))]
#[ensures([1/2]u32_own(mutex as *mut u32, v) &*& [1/2]mutex_own(mutex))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (&*mutex).lock().unwrap()
}

#[requires([1/2]u32_own(_guard as *mut u32, ?v) &*& [1/2]mutex_own(_guard as *mut Mutex))]
#[ensures([1/2]u32_own(_guard as *mut u32, v) &*& [1/2]mutex_own(_guard as *mut Mutex))]
unsafe fn release(_guard: MutexGuard) {}

#[ensures(result == true || result == false)]
unsafe fn wait_for_pulse(_source: i32) -> bool {
    true
}

#[ensures(result == 1)]
unsafe fn wait_for_source() -> i32 {
    1
}

#[requires(count_pulses_data_own(data))]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    loop
    #[invariant(thread_token(counter, mutex))]
    {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);

        // Before updating *counter, we have exclusive ownership of the u32 cell
        // via the mutex_guard combined with our thread_token halves.
        // We must reason that u32_own(counter, v) holds for some v.
        // Since we hold [1/2]u32_own(counter, _) and acquire provides [1/2]u32_own,
        // combined gives full ownership, so safe to update.
        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

#[requires(thread_token(counter, mutex))]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
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

#[requires(print_count_data_own(data))]
unsafe fn print_count(data: PrintCountData) {
    let PrintCountData { counter, mutex } = data;
    loop
    #[invariant(thread_token(counter, mutex))]
    {
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);

        println!("{}", *counter);

        release(guard);
    }
}

#[requires(thread_token(counter, mutex))]
unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex) {
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);
        loop
        #[invariant(u32_own(counter, _) &*& mutex_own(mutex))]
        {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}