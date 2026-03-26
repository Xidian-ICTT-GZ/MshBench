#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@ 
predicate counter_cell(*mut u32; u32 v) = *?ptr |-> ?w &*& w == v;
predicate mutex_initialized(*mut Mutex) = *?ptr |-> _;
predicate_ctor count_pulses_pre(CountPulsesData data)() =
    counter_cell(data.counter, ?v) &*& [_]mutex_initialized(data.mutex);
predicate_ctor print_count_pre(PrintCountData data)() =
    counter_cell(data.counter, ?v) &*& [_]mutex_initialized(data.mutex);
@*/

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
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
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [_]mutex_initialized(mutex);
//@ ens [_]mutex_initialized(mutex);
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
lem_auto count_pulses_is_spawnee()
    req true;
    ens [_]is_Spawnee(count_pulses, count_pulses_pre);
{
    close count_pulses_pre(?data)();
    leak count_pulses_pre(data)();
}
@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_pre(data)();
//@ ens true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        //@ inv counter_cell(counter, ?v) &*& [_]mutex_initialized(mutex);
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_cell(counter, ?v) &*& [_]mutex_initialized(mutex);
//@ ens true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@
lem_auto print_count_is_spawnee()
    req true;
    ens [_]is_Spawnee(print_count, print_count_pre);
{
    close print_count_pre(?data)();
    leak print_count_pre(data)();
}
@*/

unsafe fn print_count(data: PrintCountData)
//@ req print_count_pre(data)();
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;

    loop {
        //@ inv counter_cell(counter, ?v) &*& [_]mutex_initialized(mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        print_u32(*counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_cell(counter, ?v) &*& [_]mutex_initialized(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    spawn(print_count, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close counter_cell(counter, 0);

        let mutex = create_mutex();

        print_count_async(counter, mutex);

        loop {
            //@ inv counter_cell(counter, ?v) &*& [_]mutex_initialized(mutex);
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}