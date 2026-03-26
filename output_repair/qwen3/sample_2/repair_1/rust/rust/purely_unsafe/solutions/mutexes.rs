use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[verifier::predicate]
fn sendable_owns<T>(s: *Sendable<T>, t: *T) -> bool {
    std::ptr::addr_of!(s.payload) == t
}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
where
    T: Sized,
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[verifier::predicate]
fn mutex_block(m: *mut Mutex) -> bool {
    m as usize != 0
}

#[verifier::predicate]
fn counter_block(c: *mut u32) -> bool {
    c as usize != 0
}

#[verifier::predicate]
fn shared_resource(counter: *mut u32, mutex: *mut Mutex) -> bool {
    counter_block(counter) && mutex_block(mutex)
}

#[verifier::requires(true)]
#[verifier::ensures(mutex_block(result))]
unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

#[verifier::requires(mutex_block(mutex))]
#[verifier::ensures(true)]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

#[verifier::requires(true)]
#[verifier::ensures(true)]
unsafe fn release(guard: MutexGuard) {
    drop(guard);
}

#[verifier::requires(true)]
#[verifier::ensures(true)]
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[verifier::requires(true)]
#[verifier::ensures(true)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[verifier::requires(shared_resource(data.counter, data.mutex))]
#[verifier::ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        #[verifier::invariant(shared_resource(counter, mutex))]
        {
            wait_for_pulse(source);
            let guard = acquire(mutex);

            *counter = (*counter).checked_add(1).unwrap();

            release(guard);
        }
    }
}

#[verifier::requires(counter_block(counter) && mutex_block(mutex))]
#[verifier::ensures(counter_block(counter) && mutex_block(mutex))]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

#[verifier::requires(true)]
#[verifier::ensures(false)]
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
            #[verifier::invariant(counter_block(counter) && mutex_block(mutex))]
            {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                let guard = acquire(mutex);

                let count = *counter;

                release(guard);
                print_u32(count);
            }
        }
    }
}