#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

//@ pred is_Spawnee<T>(unsafe fn(T), predicate(T)) = true;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

//@ pred mutex_own(mutex: *mut Mutex; guard: MutexGuard) = true;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_own(result, _);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_own(mutex, _);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex, ?guard0);
//@ ens mutex_own(mutex, result) &*& guard0 == result;
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_own(?mutex, guard);
//@ ens mutex_own(mutex, _);
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ pred counter_mutex(counter: *mut u32, mutex: *mut Mutex) = true;

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_mutex(data.counter, data.mutex) &*& [?q]lifetime_token(?l) &*& is_Spawnee(count_pulses, counter_mutex(?c, ?m)) &*& c == data.counter &*& m == data.mutex;
//@ ens true;
{
    
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open counter_mutex(counter, mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_mutex(counter, mutex);
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_mutex(counter, mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close is_Spawnee(count_pulses, counter_mutex(counter, mutex));
    
    
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req counter_mutex(data.counter, data.mutex) &*& [?q]lifetime_token(?l) &*& is_Spawnee(print_count, counter_mutex(?c, ?m)) &*& c == data.counter &*& m == data.mutex;
//@ ens true;
{
    
    let PrintCountData {counter, mutex} = data;
    loop {
        
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open counter_mutex(counter, mutex);
        
        print_u32(*counter);
        //@ close counter_mutex(counter, mutex);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_mutex(counter, mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close is_Spawnee(print_count, counter_mutex(counter, mutex));
    
    
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close counter_mutex(counter, _);
        
        
        let mutex = create_mutex();
        //@ close counter_mutex(counter, mutex);

        print_count_async(counter, mutex);

        loop {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}