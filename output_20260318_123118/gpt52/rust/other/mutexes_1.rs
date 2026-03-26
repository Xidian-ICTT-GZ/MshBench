use std::alloc::{Layout, alloc, handle_alloc_error};

pred u32_cell(p: *mut u32, v: u32) = std::ptr::addr_of_mut!(*p) |-> v;

pred mutex_raw(m: *mut Mutex; t: std::sync::Mutex<()>) =
    std::ptr::addr_of_mut!(*m) |-> t;

pred_ctor counter_inv(counter: *mut u32)() =
    u32_cell(counter, ?v);

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

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
#[ensures(mutex_raw(result, ?t) &*& std::sync::Mutex::<()>::new_ghost_args(t, counter_inv(?c)))]
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex_raw(mutex, ?t) &*& std::sync::Mutex::<()>::mutex(mutex, t, counter_inv(?counter)))]
#[ensures(mutex_raw(mutex, t) &*& std::sync::Mutex::<()>::mutex_held(mutex, t, counter_inv(counter), result) &*& counter_inv(counter)())]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    (*mutex).lock().unwrap()
}

#[requires(std::sync::Mutex::<()>::mutex_held(?mutex, ?t, ?inv, guard) &*& inv())]
#[ensures(std::sync::Mutex::<()>::mutex(mutex, t, inv))]
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

#[requires(CountPulsesData { counter: ?counter, mutex: ?mutex, source: ?source } == data &*& mutex_raw(mutex, ?t) &*& std::sync::Mutex::<()>::mutex(mutex, t, counter_inv(counter)))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        #[invariant(mutex_raw(mutex, ?t2) &*& std::sync::Mutex::<()>::mutex(mutex, t2, counter_inv(counter)))]
        {
            wait_for_pulse(source);
            let guard = acquire(mutex);

            *counter = (*counter).checked_add(1).unwrap();

            release(guard);
        }
    }
}

#[requires(mutex_raw(mutex, ?t) &*& std::sync::Mutex::<()>::mutex(mutex, t, counter_inv(counter)))]
#[ensures(mutex_raw(mutex, t) &*& std::sync::Mutex::<()>::mutex(mutex, t, counter_inv(counter)))]
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

        //@ close u32_cell(counter, 0);
        let mutex = create_mutex();
        //@ close counter_inv(counter)();
        //@ std::sync::Mutex::<()>::init_ghost(mutex, counter_inv(counter));
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            #[invariant(mutex_raw(mutex, ?t) &*& std::sync::Mutex::<()>::mutex(mutex, t, counter_inv(counter)))]
            {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                let guard = acquire(mutex);

                let count = *counter;

                release(guard);
                print_u32(count);
            }
        }
    }
}