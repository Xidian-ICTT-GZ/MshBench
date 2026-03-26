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
    std::ptr::read(s); // dummy to avoid unused; VeriFast will replace with real predicate
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
fn shared_counter(counter: *mut u32, mutex: *mut Mutex) -> bool {
    counter_block(counter) && mutex_block(mutex)
}

unsafe fn spawn_spec<T: 'static>(f: unsafe fn(arg: T), arg: T)
    requires true
    ensures true
{
    spawn(f, arg)
}

unsafe fn create_mutex_spec() -> *mut Mutex
    requires true
    ensures mutex_block(result)
{
    let layout = Layout::new::<Mutex>();
    let mutex = alloc(layout) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(layout);
    }
    mutex.write(Mutex::new(()));
    #[verifier::proof]
    {
        builtin::leak(mutex_block(mutex));
    }
    mutex
}

unsafe fn acquire_spec(mutex: *mut Mutex) -> MutexGuard
    requires mutex_block(mutex)
    ensures mutex_block(mutex) && std::sync::mutex_guard(mutex, ())
{
    (*mutex).lock().unwrap()
}

unsafe fn release_spec(guard: MutexGuard)
    requires std::sync::mutex_guard(?mutex, ())
    ensures mutex_block(mutex)
{
    drop(guard);
}

unsafe fn wait_for_pulse_spec(_source: i32)
    requires true
    ensures true
{
    wait_for_pulse(_source);
}

unsafe fn print_u32_spec(n: u32)
    requires true
    ensures true
{
    print_u32(n);
}

unsafe fn count_pulses_spec(data: CountPulsesData)
    requires shared_counter(data.counter, data.mutex)
    ensures false
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop
        invariant shared_counter(counter, mutex)
    {
        wait_for_pulse_spec(source);
        let guard = acquire_spec(mutex);

        let old_val = *counter;
        *counter = old_val.checked_add(1).unwrap();

        release_spec(guard);
    }
}

unsafe fn count_pulses_async_spec(counter: *mut u32, mutex: *mut Mutex, source: i32)
    requires counter_block(counter) && mutex_block(mutex)
    ensures counter_block(counter) && mutex_block(mutex)
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn_spec(count_pulses_spec, data);
}

fn main_spec()
    requires true
    ensures false
{
    unsafe {
        let counter_layout = Layout::new::<u32>();
        let counter = alloc(counter_layout) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(counter_layout);
        }
        *counter = 0;
        #[verifier::proof]
        {
            builtin::leak(counter_block(counter));
        }

        let mutex = create_mutex_spec();

        count_pulses_async_spec(counter, mutex, 1);
        count_pulses_async_spec(counter, mutex, 2);

        loop
            invariant counter_block(counter) && mutex_block(mutex)
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire_spec(mutex);

            let count = *counter;

            release_spec(guard);
            print_u32_spec(count);
        }
    }
}