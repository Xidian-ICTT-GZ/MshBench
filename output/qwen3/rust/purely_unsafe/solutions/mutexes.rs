use std::alloc::{alloc, handle_alloc_error, Layout};

#[pred] 
pred mutex_inv(mutex: *mut Mutex, guard: MutexGuard) =
    mutex |-> ?m &*& m == Mutex::new(()) &*& guard |-> ?g &*& g == MutexGuard::new();

#[pred]
pred counter_pred(counter: *mut u32, value: u32) =
    counter |-> value;

#[pred]
pred count_pulses_data_pred(data: CountPulsesData, counter_val: u32) =
    data.counter |-> counter_val &*& data.mutex |-> ?m &*& m == Mutex::new(()) &*& data.source |-> ?s;

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
#[ensures mutex |-> ?m &*& m == Mutex::new(()) &*& result |-> ?g &*& g == MutexGuard::new();]
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

    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
#[requires counter |-> ?c &*& mutex |-> ?m &*& m == Mutex::new(());]
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