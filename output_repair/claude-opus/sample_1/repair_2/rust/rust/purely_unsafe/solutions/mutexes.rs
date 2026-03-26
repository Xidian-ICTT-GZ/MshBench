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

predicate mutex_inv(m: *mut Mutex) {
    m != std::ptr::null_mut()
}

predicate counter_owned(c: *mut u32) {
    c != std::ptr::null_mut()
}

predicate thread_data_owned(counter: *mut u32, mutex: *mut Mutex) {
    counter != std::ptr::null_mut() && mutex != std::ptr::null_mut()
}

#[requires(mutex_inv(mutex))]
#[ensures(mutex_inv(mutex))]
unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex_inv(mutex))]
#[ensures(mutex_inv(mutex))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

#[requires(mutex_inv(mutex))]
#[ensures(mutex_inv(mutex))]
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

#[requires(thread_data_owned(data.counter, data.mutex))]
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

#[requires(counter_owned(counter) && mutex_inv(mutex))]
#[ensures(counter_owned(counter) && mutex_inv(mutex))]
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