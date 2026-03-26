use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn mutex_pointer(m: *mut std::sync::Mutex<()>) -> bool {
    exists(|ptr: *mut std::sync::Mutex<()>| ptr == m && ptr != std::ptr::null_mut())
}

#[predicate]
fn mutex_owned(m: *mut std::sync::Mutex<()>) -> bool {
    exists(|ptr: *mut std::sync::Mutex<()>| ptr == m && ptr != std::ptr::null_mut())
}

#[predicate]
fn u32_pointer(p: *mut u32) -> bool {
    exists(|ptr: *mut u32| ptr == p && ptr != std::ptr::null_mut())
}

#[predicate]
fn u32_owned(p: *mut u32, v: u32) -> bool {
    exists(|ptr: *mut u32, val: u32| ptr == p && ptr != std::ptr::null_mut() && val == v)
}

#[predicate]
fn count_pulses_data_owned(data: CountPulsesData) -> bool {
    exists(|c: *mut u32, m: *mut std::sync::Mutex<()>, s: i32|
        data.counter == c && data.mutex == m && data.source == s &&
        c != std::ptr::null_mut() && m != std::ptr::null_mut())
}

#[requires(mutex_pointer(mutex))]
#[ensures(mutex_owned(mutex))]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[ensures(result != std::ptr::null_mut() && mutex_owned(result))]
unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex != std::ptr::null_mut() && mutex_owned(mutex))]
#[ensures(mutex_owned(mutex))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

#[requires(mutex_owned(mutex))]
unsafe fn release(guard: MutexGuard) {
    drop(guard);
}

#[requires(source >= 0)]
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(n >= 0)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires(count_pulses_data_owned(data))]
#[requires(data.source >= 0)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {counter, mutex, source} = data;
    #[invariant(counter != std::ptr::null_mut() && mutex != std::ptr::null_mut())]
    #[invariant(mutex_owned(mutex))]
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
}

#[requires(counter != std::ptr::null_mut() && mutex != std::ptr::null_mut())]
#[requires(source >= 0)]
#[requires(u32_pointer(counter))]
#[requires(mutex_pointer(mutex))]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        
        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        
        #[invariant(counter != std::ptr::null_mut() && mutex != std::ptr::null_mut())]
        #[invariant(mutex_owned(mutex))]
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            
            let count = *counter;
            
            release(guard);
            print_u32(count);
        }
    }
}