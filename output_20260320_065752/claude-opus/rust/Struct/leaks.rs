#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@ 

predicate_ptr_counter(u32 *counter) = true;

predicate_ptr_mutex(*mut Mutex mutex) = true;

predicate_sendable<T>(Sendable<T> *package; T payload) = package->payload |-> payload;

predicate is_Spawnee(unsafe fn (arg: T), predicate<T> pre) = true;

@*/

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

//@ req true;
//@ ens result != 0 &*& predicate_ptr_mutex(result);
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

//@ req predicate_ptr_mutex(mutex);
//@ ensures predicate_ptr_mutex(mutex) &*& result._mutex_guard;
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    (*mutex).lock().unwrap()
}

//@ req guard._mutex_guard;
//@ ensures true;
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
}

//@ req true;
//@ ens true;
unsafe fn wait_for_source() -> i32
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

//@ req true;
//@ ens true;
unsafe fn wait_for_pulse(_source: i32) -> bool
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

//@ req true;
//@ ens true;
unsafe fn print_u32(n: u32)
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ req predicate_ptr_counter(counter) &*& predicate_ptr_mutex(mutex);
//@ ens true;
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;

    //@ open predicate_ptr_mutex(mutex);
    loop {
        //@ close predicate_ptr_mutex(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        //@ open predicate_ptr_counter(counter);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close predicate_ptr_counter(counter);
        
        release(guard);
        //@ open predicate_ptr_mutex(mutex);
    }
    //@ close predicate_ptr_mutex(mutex);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req predicate_ptr_counter(counter) &*& predicate_ptr_mutex(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

//@ req predicate_ptr_counter(counter) &*& predicate_ptr_mutex(mutex);
//@ ens true;
unsafe fn print_count(data: PrintCountData)
{
    let PrintCountData {counter, mutex} = data;
    //@ open predicate_ptr_mutex(mutex);
    loop {
        //@ close predicate_ptr_mutex(mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open predicate_ptr_counter(counter);
        print_u32(*counter);
        //@ close predicate_ptr_counter(counter);
        release(guard);
        //@ open predicate_ptr_mutex(mutex);
    }
    //@ close predicate_ptr_mutex(mutex);
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req predicate_ptr_counter(counter) &*& predicate_ptr_mutex(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    
    spawn(print_count, data);
}

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close predicate_ptr_counter(counter);
        
        let mutex = create_mutex();
        //@ close predicate_ptr_mutex(mutex);

        print_count_async(counter, mutex);

        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
        //@ open predicate_ptr_counter(counter);
        //@ open predicate_ptr_mutex(mutex);
    }
}