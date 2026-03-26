#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@
pred mutex_own(?p) = true;
pred mutex(?p) = true;
pred u32_own(?p, ?v) = true;
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

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_own(result) &*& mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex) &*& mutex(mutex);
//@ ens mutex_own(mutex) &*& mutex(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
//@ ens true;
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

/*@
pred CountPulsesData_own(data: CountPulsesData) =
    u32_own(data.counter, ?counter_val) &*&
    mutex_own(data.mutex) &*&
    mutex(data.mutex) &*&
    data.source |-> ?source_val;
@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data);
//@ ens true;
{
    //@ open CountPulsesData_own(data);
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ inv u32_own(counter, ?counter_val) &*& mutex_own(mutex) &*& mutex(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open u32_own(counter, ?old_val);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close u32_own(counter, old_val + 1);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req u32_own(counter, ?counter_val) &*& mutex_own(mutex) &*& mutex(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_own(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@
pred PrintCountData_own(data: PrintCountData) =
    u32_own(data.counter, ?counter_val) &*&
    mutex_own(data.mutex) &*&
    mutex(data.mutex);
@*/

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ens true;
{
    //@ open PrintCountData_own(data);
    let PrintCountData {counter, mutex} = data;
    loop {
        //@ inv u32_own(counter, ?counter_val) &*& mutex_own(mutex) &*& mutex(mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open u32_own(counter, ?val);
        print_u32(*counter);
        //@ close u32_own(counter, val);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req u32_own(counter, ?counter_val) &*& mutex_own(mutex) &*& mutex(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data);
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
        //@ close u32_own(counter, 0);
        
        let mutex = create_mutex();
        //@ assert mutex_own(mutex) &*& mutex(mutex);

        print_count_async(counter, mutex);

        loop {
            //@ inv u32_own(counter, ?counter_val) &*& mutex_own(mutex) &*& mutex(mutex);
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}