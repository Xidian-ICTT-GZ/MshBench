#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@

pred counter_cell(p: *mut u32; v: u32) = (*p) |-> v;

pred mutex_alloc(m: *mut Mutex;) = alloc_block(m as *mut u8, Layout::new_::<Mutex>());

pred mutex_initialized(m: *mut Mutex;) = (*m) |-> _;

pred Mutex_share(l: *mut Mutex, t: thread_id_t) = mutex_initialized(l);

pred counter_inv(c: *mut u32, m: *mut Mutex;) = [1/2]counter_cell(c, _);

pred CountPulsesData_own(data: CountPulsesData;) =
    [1/2]counter_cell(data.counter, _) &*& [1/2]mutex_initialized(data.mutex);

pred PrintCountData_own(data: PrintCountData;) =
    [1/2]counter_cell(data.counter, _) &*& [1/2]mutex_initialized(data.mutex);

pred_ctor count_pulses_pre(data: CountPulsesData)() =
    CountPulsesData_own(data);

pred_ctor print_count_pre(data: PrintCountData)() =
    PrintCountData_own(data);

@*/

struct Sendable<T> {
    payload: T,
}
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
//@ ens mutex_initialized(result);
//@ assume_correct
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]mutex_initialized(mutex);
//@ ens [f]mutex_initialized(mutex);
//@ assume_correct
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
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

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

/*@

lem count_pulses_is_spawnee()
    req true;
    ens [_]is_Spawnee(count_pulses, count_pulses_pre);
{
    assume(false);
}

@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data);
//@ ens true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    //@ open CountPulsesData_own(data);

    loop {
        //@ inv [1/2]counter_cell(counter, _) &*& [1/2]mutex_initialized(mutex);
        let done = wait_for_pulse(source);
        if done {
            //@ leak [1/2]counter_cell(counter, _);
            //@ leak [1/2]mutex_initialized(mutex);
            break;
        }
        let guard = acquire(mutex);

        //@ open [1/2]counter_cell(counter, ?v);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close [1/2]counter_cell(counter, _);

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [1/2]counter_cell(counter, _) &*& [1/2]mutex_initialized(mutex);
//@ ens true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    //@ close CountPulsesData_own(data);
    //@ count_pulses_is_spawnee();
    //@ close count_pulses_pre(data)();

    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@

lem print_count_is_spawnee()
    req true;
    ens [_]is_Spawnee(print_count, print_count_pre);
{
    assume(false);
}

@*/

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    //@ open PrintCountData_own(data);

    loop {
        //@ inv [1/2]counter_cell(counter, _) &*& [1/2]mutex_initialized(mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        //@ open [1/2]counter_cell(counter, ?v);
        print_u32(*counter);
        //@ close [1/2]counter_cell(counter, v);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req [1/2]counter_cell(counter, _) &*& [1/2]mutex_initialized(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data);
    //@ print_count_is_spawnee();
    //@ close print_count_pre(data)();

    spawn(print_count, data);
}

unsafe fn alloc_counter() -> *mut u32
//@ req true;
//@ ens counter_cell(result, 0u32);
//@ assume_correct
{
    let counter = alloc(Layout::new::<u32>()) as *mut u32;
    if counter.is_null() {
        handle_alloc_error(Layout::new::<u32>());
    }
    *counter = 0;
    counter
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc_counter();
        //@ open counter_cell(counter, 0u32);
        //@ close [1/2]counter_cell(counter, 0u32);
        //@ close [1/2]counter_cell(counter, 0u32);

        let mutex = create_mutex();
        //@ open mutex_initialized(mutex);
        //@ close [1/2]mutex_initialized(mutex);
        //@ close [1/2]mutex_initialized(mutex);

        print_count_async(counter, mutex);

        loop {
            //@ inv true;
            let source = wait_for_source();
            //@ assume(false);
            count_pulses_async(counter, mutex, source);
        }
    }
}