use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

predicate sendable_owns<T>(s: *mut Sendable<T>, t: *mut T) = (*s).payload |-> ?v &*& t == &(*s).payload as *const _ as *mut T;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
    requires T::own(arg);
    ensures true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

predicate mutex_block(m: *mut Mutex) = *m |-> ?unit &*& [_]std::sync::mutex_token(?t);

predicate counter_block(c: *mut u32) = *c |-> ?n;

predicate shared_counter(counter: *mut u32, mutex: *mut Mutex) =
    counter_block(counter) &*& mutex_block(mutex);

unsafe fn create_mutex() -> *mut Mutex
    requires true;
    ensures mutex_block(result);
{
    let layout = Layout::new::<Mutex>();
    let mutex = alloc(layout) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(layout);
    }
    mutex.write(Mutex::new(()));
    leak mutex_block(mutex);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
    requires mutex_block(mutex);
    ensures mutex_block(mutex) &*& std::sync::mutex_guard(mutex, ());
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
    requires std::sync::mutex_guard(?mutex, ());
    ensures mutex_block(mutex);
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
    requires true;
    ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
    requires true;
    ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
    requires shared_counter(data.counter, data.mutex);
    ensures false;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop
        invariant shared_counter(counter, mutex);
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        let old_val = *counter;
        *counter = old_val.checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
    requires counter_block(counter) &*& mutex_block(mutex);
    ensures counter_block(counter) &*& mutex_block(mutex);
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

fn main()
    requires true;
    ensures false;
{
    unsafe {
        let counter_layout = Layout::new::<u32>();
        let counter = alloc(counter_layout) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(counter_layout);
        }
        *counter = 0;
        leak counter_block(counter);

        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop
            invariant counter_block(counter) &*& mutex_block(mutex);
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}