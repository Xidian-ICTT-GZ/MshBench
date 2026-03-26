use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard) {
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}

#[verifier::predicate]
fn sendable_owns<T>(s: *mut Sendable<T>) -> bool {
    std::ptr::read(s); // dummy to satisfy syntax; VeriFast ignores body
    false
}

#[verifier::predicate]
fn mutex_block(m: *mut Mutex) -> bool {
    std::ptr::read(m);
    false
}

#[verifier::predicate]
fn counter_block(c: *mut u32) -> bool {
    std::ptr::read(c);
    false
}

#[verifier::predicate]
fn shared_resource(counter: *mut u32, mutex: *mut Mutex) -> bool {
    counter_block(counter) && mutex_block(mutex)
}

#[requires(true)]
#[ensures(true)]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

#[requires(true)]
#[ensures(mutex_block(result))]
unsafe fn create_mutex() -> *mut Mutex {
    let layout = Layout::new::<Mutex>();
    let mutex = alloc(layout) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(layout);
    }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex_block(mutex))]
#[ensures(mutex_block(mutex))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

#[requires(true)]
#[ensures(true)]
unsafe fn release(guard: MutexGuard) {
    drop(guard);
}

#[requires(true)]
#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

#[requires(shared_resource(data.counter, data.mutex))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    #[invariant(shared_resource(counter, mutex))]
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

#[requires(counter_block(counter) * mutex_block(mutex))]
#[ensures(counter_block(counter) * mutex_block(mutex))]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

#[requires(true)]
#[ensures(false)]
fn main() {
    unsafe {
        let layout = Layout::new::<u32>();
        let counter = alloc(layout) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(layout);
        }
        *counter = 0;

        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        #[invariant(counter_block(counter) * mutex_block(mutex))]
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}