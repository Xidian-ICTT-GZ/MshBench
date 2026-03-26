use std::alloc::{Layout, alloc, handle_alloc_error};

#[pred]
pred mutex_inv(mutex: *mut Mutex) =
    mutex |-> ?m_ptr &*&
    m_ptr != std::ptr::null_mut() &*&
    m_ptr |-> Mutex(());

#[pred]
pred mutex_guard_inv(guard: MutexGuard) =
    guard |-> MutexGuard(());

#[pred]
pred counter_inv(counter: *mut u32, v: u32) =
    counter |-> v;

#[predicate]
pred count_pulses_data_inv(data: CountPulsesData) =
    counter_inv(data.counter, ?c) &*&
    mutex_inv(data.mutex) &*&
    data.source == ?s;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
#[requires(
    count_pulses_data_inv(arg) &*&
    f == count_pulses
)]
#[ensures(
    true
)]
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
#[requires(
    true
)]
#[ensures(
    result |-> Mutex(())
)]
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
#[requires(
    mutex |-> Mutex(())
)]
#[ensures(
    mutex |-> Mutex(()) &*&
    result |-> MutexGuard(())
)]
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
#[requires(
    guard |-> MutexGuard(())
)]
#[ensures(
    true
)]
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
#[requires(
    true
)]
#[ensures(
    true
)]
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
#[requires(
    true
)]
#[ensures(
    true
)]
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
#[requires(
    count_pulses_data_inv(data)
)]
#[ensures(
    false
)]
{
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        #[invariant(
            counter_inv(counter, ?c) &*&
            mutex |-> Mutex(()) &*&
            guard |-> MutexGuard(())
        )]
        {
            *counter = c + 1;
        }
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
#[requires(
    counter |-> ?c &*&
    mutex |-> Mutex(()) &*&
    true
)]
#[ensures(
    true
)]
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

fn main()
#[requires(
    true
)]
#[ensures(
    true
)]
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
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