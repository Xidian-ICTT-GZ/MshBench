use std::alloc::{Layout, alloc, handle_alloc_error};

#[pred]
pred mutex_inv(mutex: *mut Mutex) = mutex |-> ?m &*& m == Mutex(());

#[pred]
pred guard_inv(guard: MutexGuard) = guard |-> ?g &*& g == MutexGuard(());

#[pred]
pred locked_mutex(mutex: *mut Mutex, guard: MutexGuard) =
    mutex_inv(mutex) &*& guard_inv(guard);

#[pred]
pred counter_inv(counter: *mut u32, value: u32) = counter |-> value;

#[pred]
pred count_pulses_data_inv(data: CountPulsesData) =
    counter_inv(data.counter, ?c) &*& mutex_inv(data.mutex) &*&
    data.source |-> ?s &*& s == data.source;

unsafe fn spawn<T: 'static + Copy>(f: unsafe fn(arg: T), arg: T)
#[requires(
    count_pulses_data_inv(arg)
    &*& f == count_pulses
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
    mutex_inv(result)
)]
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
#[requires(
    mutex_inv(mutex)
)]
#[ensures(
    locked_mutex(mutex, result)
)]
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
#[requires(
    guard_inv(guard)
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
    counter_inv(data.counter, ?c0)
    &*& mutex_inv(data.mutex)
    &*& data.source |-> ?s
)]
#[ensures(
    false
)]
{
    let CountPulsesData { counter, mutex, source } = data;
    let mut local_counter = c0;
    loop {
        wait_for_pulse(source);

        let guard = acquire(mutex);
        #[invariant(
            counter_inv(counter, local_counter)
            &*& locked_mutex(mutex, guard)
        )]
        {
            let old_v = *counter;
            let new_v = old_v.checked_add(1).unwrap();
            *counter = new_v;
            local_counter = new_v;
        }
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
#[requires(
    counter_inv(counter, ?c)
    &*& mutex_inv(mutex)
    &*& true
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
            #[invariant(
                counter_inv(counter, ?count) &*& locked_mutex(mutex, guard)
            )]
            {
                let count = *counter;
                // Note: count is read while holding the mutex
            }
            release(guard);
            print_u32(*counter);
        }
    }
}