#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@

pred Mutex(mutex: *mut Mutex; P: pred());

pred Mutex_held(mutex: *mut Mutex, guard: MutexGuard, P: pred());

pred counter_inv(counter: *mut u32)() =
    alloc_block_u32(counter) &*& *counter |-> ?_;

pred_ctor is_Spawnee(f: unsafe fn(T), pre: pred(T))() = true;

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
//@ ens Mutex(result, counter_inv(?counter));
//@ assume_correct
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]Mutex(mutex, ?P);
//@ ens Mutex_held(mutex, result, P) &*& P() &*& [f]Mutex(mutex, P);
//@ assume_correct
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req Mutex_held(?mutex, guard, ?P) &*& P();
//@ ens true;
//@ assume_correct
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
//@ assume_correct
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
//@ assume_correct
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", n);
}

/*@

pred CountPulsesData_own(data: CountPulsesData) =
    [_]Mutex(data.mutex, counter_inv(data.counter));

@*/

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

/*@

pred_ctor count_pulses_pre()(data: CountPulsesData) =
    CountPulsesData_own(data);

@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data);
//@ ens true;
{
    //@ open CountPulsesData_own(data);
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ inv [_]Mutex(mutex, counter_inv(counter));
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open counter_inv(counter)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_inv(counter)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [_]Mutex(mutex, counter_inv(counter));
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_own(data);
    //@ close count_pulses_pre()(data);
    //@ close is_Spawnee(count_pulses, count_pulses_pre)();
    //@ leak is_Spawnee(count_pulses, count_pulses_pre)();
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@

pred PrintCountData_own(data: PrintCountData) =
    [_]Mutex(data.mutex, counter_inv(data.counter));

pred_ctor print_count_pre()(data: PrintCountData) =
    PrintCountData_own(data);

@*/

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ens true;
{
    //@ open PrintCountData_own(data);
    let PrintCountData {counter, mutex} = data;
    loop {
        //@ inv [_]Mutex(mutex, counter_inv(counter));
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open counter_inv(counter)();
        print_u32(*counter);
        //@ close counter_inv(counter)();
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req [_]Mutex(mutex, counter_inv(counter));
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data);
    //@ close print_count_pre()(data);
    //@ close is_Spawnee(print_count, print_count_pre)();
    //@ leak is_Spawnee(print_count, print_count_pre)();
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
        //@ close alloc_block_u32(counter);
        *counter = 0;
        
        let mutex = create_mutex();
        //@ assume(Mutex(mutex, counter_inv(counter)));
        //@ leak Mutex(mutex, counter_inv(counter));

        print_count_async(counter, mutex);

        loop {
            //@ inv [_]Mutex(mutex, counter_inv(counter));
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}