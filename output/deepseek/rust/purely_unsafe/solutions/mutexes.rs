use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn sendable<T>(s: &Sendable<T>) -> bool { true }

#[predicate]
fn sendable_owned<T>(s: Sendable<T>) -> bool { true }

#[predicate]
fn mutex_points_to(m: *mut Mutex, v: ()) -> bool { true }

#[predicate]
fn mutex_frac(m: *mut Mutex, f: rational) -> bool { true }

#[predicate]
fn u32_points_to(p: *mut u32, v: u32) -> bool { true }

#[predicate]
fn count_pulses_data_owned(data: CountPulsesData) -> bool { true }

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
    #[requires(sendable_owned(Sendable { payload: arg }))]
    #[ensures(true)]
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
    #[ensures(mutex_points_to(result, ()))]
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
    #[requires(mutex_points_to(mutex, ()))]
    #[ensures(mutex_points_to(mutex, ()))]
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
    #[requires(mutex_points_to(guard.mutex().unwrap() as *mut Mutex, ()))]
    #[ensures(true)]
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
    #[ensures(true)]
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
    #[ensures(true)]
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
    #[requires(count_pulses_data_owned(data))]
    #[ensures(false)]
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        #[invariant(mutex_points_to(mutex, ()))]
        #[invariant(u32_points_to(counter, ?v))]
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
    #[requires(u32_points_to(counter, ?v))]
    #[requires(mutex_points_to(mutex, ()))]
    #[ensures(true)]
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    #[proof] let data_pred = count_pulses_data_owned(data);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        #[proof] let counter_pred = u32_points_to(counter, 0);

        let mutex = create_mutex();
        #[proof] let mutex_pred = mutex_points_to(mutex, ());

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