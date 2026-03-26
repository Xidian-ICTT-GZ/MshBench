use std::alloc::{Layout, alloc, handle_alloc_error};

predicate mutex(Mutex* mutex, bool locked);

predicate counter(uint32_t* counter, int count) = 
  counter |-> count;

predicate sendable<T>(Sendable<T>* p, T payload) =
  p->payload |-> payload;

predicate count_pulses_data(CountPulsesData* data, uint32_t* counter, Mutex* mutex, int source) =
  data->counter |-> counter &*&
  data->mutex |-> mutex &*&
  data->source |-> source;

#[requires(true)]
#[ensures(mutex(result, false))]
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex(mutex, false))]
#[ensures(mutex(mutex, true))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    (*mutex).lock().unwrap()
}

#[requires(mutex(mutex, true))]
#[ensures(mutex(mutex, false))]
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
}

#[predicate_family_instance opaque_sendable<T>(Sendable<T>* p) = sendable(p, *p)]
#[requires(sendable(package, arg))]
#[ensures(true)]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

#[requires(true)]
#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32)
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u32(_n: u32)
{
    println!("{}", _n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires(count_pulses_data(data, counter, mutex, source) &*& counter(counter, ?c) &*& mutex(mutex, false))]
#[ensures(true)]
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;
    while (true)
        invariant count_pulses_data(&data, counter, mutex, source) &*& counter(counter, ?count) &*& mutex(mutex, false);
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        // must have ownership of counter
        // dereference counter requires counter predicate with fractional permission,
        // here we assume full ownership for simplicity.
        let old_count = *counter;
        *counter = old_count.checked_add(1).unwrap();
        release(guard);
    }
}

#[requires(counter(counter, _) &*& mutex(mutex, false))]
#[ensures(true)]
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
        while (true)
            invariant counter(counter, ?c) &*& mutex(mutex, false);
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            let count = *counter;
            release(guard);
            print_u32(count);
        }
    }
}