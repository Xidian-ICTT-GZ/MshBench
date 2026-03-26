use std::alloc::{Layout, alloc, handle_alloc_error};

predicate u32_own(ptr: *mut u32; val: u32) = (*ptr) |-> val;
predicate mutex_own(ptr: *mut Mutex) = (*ptr) |-> ?guard_content &*& is_Mutex(guard_content);
predicate CountPulsesData_full(data: *CountPulsesData) =
    data as *mut CountPulsesData |-> ?fields &*&
    struct_CountPulsesData_padding(fields) &*&
    u32_own(fields.counter, ?val) &*&
    mutex_own(fields.mutex) &*&
    fields.source |-> ?src;

#[requires(true)]
#[ensures(true)]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[requires(true)]
#[ensures(mutex_own(result))]
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex_own(mutex))]
#[ensures(mutex_guard_full(result, mutex))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    (*mutex).lock().unwrap()
}

predicate mutex_guard_full(guard: MutexGuard, mutex: *mut Mutex) =
    guard as *mut () == mutex as *mut ();

#[requires(mutex_guard_full(guard, ?mutex))]
#[ensures(mutex_own(mutex))]
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
}

#[requires(true)]
#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32)
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u32(n: u32)
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires(CountPulsesData_full(data))]
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;
    loop
        invariant u32_own(counter, ?val) &*& mutex_own(mutex) &*& source |-> ?src;
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        let old_val = *counter;
        *counter = old_val.checked_add(1).unwrap();

        release(guard);
    }
}

#[requires(u32_own(counter, _) &*& mutex_own(mutex))]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;

        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop
            invariant u32_own(counter, ?val) &*& mutex_own(mutex);
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}