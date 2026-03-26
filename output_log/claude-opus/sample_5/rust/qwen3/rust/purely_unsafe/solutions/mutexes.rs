use std::alloc::{alloc, handle_alloc_error, Layout};

#[pred]
pred mutex_pred(mutex: *mut Mutex) =
    mutex |-> _ &*& 0 <= _; // dummy ownership to hold pointer (no interior fields)

#[pred]
pred mutex_guard_pred(guard: MutexGuard) =
    true; // The MutexGuard lifetime token, no heap data owned explicitly here

#[pred]
pred counter_pred(counter: *mut u32, value: u32) =
    counter |-> value;

#[pred]
pred count_pulses_data_pred(data: CountPulsesData, counter_val: u32) =
    data.counter |-> counter_val &*&
    mutex_pred(data.mutex) &*&
    0 <= data.source; // source is i32 but only positive needed here for example (could be any condition)

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
#[requires true]
#[ensures true]
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
#[requires true]
#[ensures result |-> ?m &*& m == Mutex::new(());]
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
#[requires mutex |-> ?m &*& m == Mutex::new(());]
#[ensures mutex |-> m &*& result |-> ?g &*& g == MutexGuard::new();]
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
#[requires guard |-> ?g &*& g == MutexGuard::new();]
#[ensures true]
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
#[requires true]
#[ensures true]
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
#[requires true]
#[ensures true]
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
#[requires count_pulses_data_pred(data, ?c);]
#[ensures false;] // diverges
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    predicate counter_mutex_inv(counter: *mut u32, mutex: *mut Mutex, val: u32) =
        counter |-> val &*& mutex_pred(mutex);

    open count_pulses_data_pred(data, c);

    fixpoint void loop_invariant(u32 val) =
        counter_mutex_inv(counter, mutex, val);

    let mut val = c;
    loop
    #[invariant counter_mutex_inv(counter, mutex, val)]
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        //@ open counter_mutex_inv(counter, mutex, val);
        val = val + 1;
        *counter = val;
        //@ close counter_mutex_inv(counter, mutex, val);

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
#[requires counter |-> ?c &*& mutex_pred(mutex)]
#[ensures true]
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

fn main()
#[requires true]
#[ensures true]
{
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