use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn mutex_pointer(m: *mut Mutex) -> bool { true }

#[predicate]
fn mutex_pointer_frac(m: *mut Mutex, f: real) -> bool { true }

#[predicate]
fn mutex_pointer_full(m: *mut Mutex) -> bool { 
    mutex_pointer_frac(m, 1.0)
}

#[predicate]
fn mutex_pointer_half(m: *mut Mutex) -> bool { 
    mutex_pointer_frac(m, 0.5)
}

#[predicate]
fn u32_pointer(p: *mut u32) -> bool { true }

#[predicate]
fn u32_pointer_frac(p: *mut u32, f: real) -> bool { true }

#[predicate]
fn u32_pointer_full(p: *mut u32) -> bool { 
    u32_pointer_frac(p, 1.0)
}

#[predicate]
fn u32_pointer_half(p: *mut u32) -> bool { 
    u32_pointer_frac(p, 0.5)
}

#[predicate]
fn mutex_guard(g: MutexGuard) -> bool { true }

#[predicate]
fn count_pulses_data_owned(data: CountPulsesData) -> bool { 
    u32_pointer_half(data.counter) && 
    mutex_pointer_half(data.mutex)
}

#[predicate]
fn count_pulses_data_shared(data: CountPulsesData) -> bool { 
    u32_pointer_half(data.counter) && 
    mutex_pointer_half(data.mutex)
}

#[requires(u32_pointer_full(counter))]
#[ensures(u32_pointer_full(counter))]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[ensures(result != std::ptr::null_mut() && mutex_pointer_full(result))]
unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex != std::ptr::null_mut() && mutex_pointer_full(mutex))]
#[ensures(mutex_guard(result) && mutex_pointer_full(mutex))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

#[requires(mutex_guard(guard))]
#[ensures(true)]
unsafe fn release(guard: MutexGuard) {
    drop(guard);
}

#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires(count_pulses_data_owned(data))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

#[requires(
    counter != std::ptr::null_mut() && 
    mutex != std::ptr::null_mut() && 
    u32_pointer_full(counter) && 
    mutex_pointer_full(mutex)
)]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

#[ensures(false)]
fn main() {
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