use std::alloc::{Layout, alloc, handle_alloc_error};

#[predicate]
fn u32_own(p: *mut u32, v: u32) -> bool {
    exists!(v0: u32; true) && 
    p != std::ptr::null_mut() && 
    *p |-> v && v == v0
}

#[predicate]
fn mutex_own(p: *mut Mutex) -> bool {
    p != std::ptr::null_mut() && 
    *p |-> std::sync::Mutex::new(())
}

#[predicate]
fn mutex_guard_own(g: MutexGuard) -> bool {
    exists!(m: *mut Mutex; true) && 
    g == (*m).lock().unwrap()
}

#[predicate]
fn count_pulses_data_own(data: CountPulsesData) -> bool {
    exists!(counter: *mut u32, mutex: *mut Mutex, source: i32;
        data.counter == counter && 
        data.mutex == mutex && 
        data.source == source && 
        u32_own(counter, 0) && 
        mutex_own(mutex)
    )
}

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[requires(exists!(arg: T; true))]
#[ensures(true)]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

#[requires(Layout::new::<Mutex>().size() > 0)]
#[ensures(result != std::ptr::null_mut() && mutex_own(result))]
unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires(mutex != std::ptr::null_mut() && mutex_own(mutex))]
#[ensures(mutex_guard_own(result))]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

#[requires(mutex_guard_own(guard))]
#[ensures(true)]
unsafe fn release(guard: MutexGuard) {
    drop(guard);
}

#[requires(source >= 0)]
#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(n >= 0)]
#[ensures(true)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires(count_pulses_data_own(data))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {counter, mutex, source} = data;
    #[invariant(counter != std::ptr::null_mut() && mutex != std::ptr::null_mut())]
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
    source >= 0 && 
    u32_own(counter, 0) && 
    mutex_own(mutex)
)]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
    let data = CountPulsesData { counter, mutex, source };
    
    spawn(count_pulses, data);
}

#[requires(Layout::new::<u32>().size() > 0)]
#[ensures(true)]
fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        
        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        
        #[invariant(counter != std::ptr::null_mut() && mutex != std::ptr::null_mut())]
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            
            let count = *counter;
            
            release(guard);
            print_u32(count);
        }
    }
}