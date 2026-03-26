#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
predicate u32_own(counter: *mut u32, v: u32) =
    counter |-> v;

predicate_ctor mutex_inv(counter: *mut u32)() =
    u32_own(counter, ?v);

predicate counter_shared(counter: *mut u32, mutex: *mut Mutex) =
    [1/2]pointer(mutex, _) &*& [1/2]mutex(mutex, mutex_inv(counter)) &*&
    u32_own(counter, _);

predicate CountPulsesData_own(data: CountPulsesData) =
    data.counter |-> ?counter_val &*& data.mutex |-> ?mutex_val &*& data.source |-> _ &*&
    counter_shared(counter_val, mutex_val);

predicate PrintCountData_own(data: PrintCountData) =
    data.counter |-> ?counter_val &*& data.mutex |-> ?mutex_val &*&
    counter_shared(counter_val, mutex_val);
@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ensures true;
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
//@ req u32_own(?counter, _);
//@ ensures pointer(result, _) &*& mutex(result, mutex_inv(counter));
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    //@ close mutex_inv(counter)();
    //@ create_mutex(mutex, mutex_inv(counter));
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]pointer(mutex, _) &*& [f]mutex(mutex, ?inv);
//@ ensures [f]pointer(mutex, _) &*& [f]mutex(mutex, inv) &*& mutex_guard(result, inv) &*& inv();
{
    //@ acquire_mutex(mutex);
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(guard, ?inv) &*& inv();
//@ ensures true;
{
    //@ release_mutex(guard);
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data);
//@ ensures true;
{
    //@ open CountPulsesData_own(data);
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    //@ open counter_shared(counter, mutex);

    loop
    //@ inv [1/2]pointer(mutex, _) &*& [1/2]mutex(mutex, mutex_inv(counter)) &*& u32_own(counter, _);
    {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);
        //@ open mutex_inv(counter)();
        u32_own(counter, ?old_v);
        let new_v = old_v + 1;
        *counter = new_v;
        //@ close u32_own(counter, new_v);
        //@ close mutex_inv(counter)();
        release(guard);
    }
    //@ leak pointer(mutex, _);
    //@ leak mutex(mutex, mutex_inv(counter));
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_shared(counter, mutex);
//@ ensures true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    //@ close CountPulsesData_own(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ensures true;
{
    //@ open PrintCountData_own(data);
    let PrintCountData { counter, mutex } = data;
    //@ open counter_shared(counter, mutex);
    loop
    //@ inv [1/2]pointer(mutex, _) &*& [1/2]mutex(mutex, mutex_inv(counter)) &*& u32_own(counter, _);
    {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex_inv(counter)();
        let v = *counter;
        print_u32(v);
        //@ close mutex_inv(counter)();
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_shared(counter, mutex);
//@ ensures true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data);
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ensures true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close u32_own(counter, 0);

        let mutex = create_mutex();
        //@ close counter_shared(counter, mutex);
        //@ close counter_shared(counter, mutex);

        print_count_async(counter, mutex);

        loop
        //@ inv counter_shared(counter, mutex);
        {
            let source = wait_for_source();
            //@ close counter_shared(counter, mutex);
            count_pulses_async(counter, mutex, source);
        }
    }
}