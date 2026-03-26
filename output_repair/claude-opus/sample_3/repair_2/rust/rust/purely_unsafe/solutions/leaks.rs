#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@
predicate counter_cell(p: *mut u32, v: u32) = (*p) |-> v;

predicate mutex_protected_counter(m: *mut Mutex, p: *mut u32) =
    (*m) |-> _ &*& counter_cell(p, _);

predicate shared_counter(m: *mut Mutex, p: *mut u32) =
    [_](*m) |-> _ &*& [_]counter_cell(p, _);

predicate count_pulses_pre(data: CountPulsesData) =
    mutex_protected_counter(data.mutex, data.counter);

predicate print_count_pre(data: PrintCountData) =
    mutex_protected_counter(data.mutex, data.counter);
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
//@ ens (*result) |-> _;
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [_](*mutex) |-> _;
//@ ens [_](*mutex) |-> _;
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

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_pre(data);
//@ ens true;
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        //@ inv [_](*mutex) |-> _ &*& (*counter) |-> _;
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
//@ req [_]is_Spawnee(count_pulses, count_pulses_pre) &*& mutex_protected_counter(mutex, counter);
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

unsafe fn print_count(data: PrintCountData)
//@ req print_count_pre(data);
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv [_](*mutex) |-> _ &*& (*counter) |-> _;
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        print_u32(*counter);

        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req [_]is_Spawnee(print_count, print_count_pre) &*& mutex_protected_counter(mutex, counter);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

fn main() {
    unsafe {
        //@ open_full_fraction(counter_cell);
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close counter_cell(counter, 0);

        let mutex = create_mutex();
        //@ close mutex_protected_counter(mutex, counter);

        print_count_async(counter, mutex);

        loop {
            //@ inv [_](*mutex) |-> _ &*& [_](*counter) |-> _;
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}