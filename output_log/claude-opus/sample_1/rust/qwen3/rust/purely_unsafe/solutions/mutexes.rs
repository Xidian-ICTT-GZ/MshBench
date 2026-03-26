use std::alloc::{alloc, handle_alloc_error, Layout};
use std::ptr::write;

#[pred]
pred mutex(mutex_ptr: *mut Mutex) = mutex_ptr |-> ?m &*& m == Mutex::new(());

#[pred]
pred mutexguard(guard: MutexGuard) = guard |-> ?g &*& g == MutexGuard::new();

#[pred]
pred counter(counter_ptr: *mut u32, value: u32) = counter_ptr |-> value;

#[pred]
pred count_pulses_data_pred(data: CountPulsesData, c: u32) =
    data.counter |-> c &*& mutex(data.mutex) &*& data.source |-> ?s;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
#[requires exists<p>::true;]
#[ensures true;]
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

unsafe fn acquire(mutex_ptr: *mut Mutex) -> MutexGuard
#[requires mutex(mutex_ptr)]
#[ensures mutex(mutex_ptr) &*& mutexguard(result);]
{
    (*mutex_ptr).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
#[requires mutexguard(guard)]
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
#[requires count_pulses_data_pred(data, ?c)]
#[ensures false;]
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    let mut curr = c;
    loop
    #[invariant count_pulses_data_pred(data, curr)]
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        // Have ownership of *counter via predicate; update it.
        // Reading and writing requires ownership via counter predicate.
        // Reconstruct predicate after update.
        counter(counter, curr) :==> // ghost function symbol for update (symbolic, here implicit)
        write(counter, curr + 1);
        curr = curr + 1;

        // predicate updated to new counter value
        assume count_pulses_data_pred(data, curr);

        release(guard);
    }
}

unsafe fn count_pulses_async(counter_ptr: *mut u32, mutex_ptr: *mut Mutex, source: i32)
#[requires counter(counter_ptr, ?c) &*& mutex(mutex_ptr)]
#[ensures true]
{
    let data = CountPulsesData {
        counter: counter_ptr,
        mutex: mutex_ptr,
        source: source,
    };

    spawn(count_pulses, data);
}

fn main()
#[requires true]
#[ensures true]
{
    unsafe {
        let counter_ptr = alloc(Layout::new::<u32>()) as *mut u32;
        if counter_ptr.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        write(counter_ptr, 0);

        let mutex_ptr = create_mutex();

        count_pulses_async(counter_ptr, mutex_ptr, 1);
        count_pulses_async(counter_ptr, mutex_ptr, 2);

        loop
        #[invariant counter(counter_ptr, ?cnt) &*& mutex(mutex_ptr)]
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex_ptr);

            let count = *counter_ptr;

            release(guard);
            print_u32(count);
        }
    }
}