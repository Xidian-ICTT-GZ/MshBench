use std::alloc::{handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn sendable_owns<T>(s: *const Sendable<T>, t: T) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[predicate]
fn mutex_alloc(m: *mut Mutex) = m as usize != 0;

#[predicate]
fn counter_alloc(c: *mut u32) = c as usize != 0;

#[predicate]
fn shared_counter(counter: *mut u32, mutex: *mut Mutex) = 
    counter_alloc(counter) && mutex_alloc(mutex);

#[requires(mutex_alloc(result))]
unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex_alloc(mutex))]
#[ensures(mutex_alloc(result))]
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

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires(shared_counter(data.counter, data.mutex))]
#[ensures(shared_counter(data.counter, data.mutex))]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    #[invariant(shared_counter(counter, mutex))]
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

#[requires(counter_alloc(counter) && mutex_alloc(mutex))]
#[ensures(counter_alloc(counter) && mutex_alloc(mutex))]
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

        #[invariant(counter_alloc(counter) && mutex_alloc(mutex))]
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}

extern "C" {
    fn alloc(layout: Layout) -> *mut u8;
}