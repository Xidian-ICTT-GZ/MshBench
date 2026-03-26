#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@
predicate counter_cell(*mut u32; u32) = *?p |-> ?v &*& p == result &*& v == arg;

predicate mutex_initialized(*mut Mutex) = *?p |-> ?m &*& p == result;

predicate shared_counter(*mut Mutex, *mut u32) =
    [_]mutex_initialized(?m) &*& exists(?v, counter_cell(?c, v)) &*& m == ?m &*& c == ?c;

predicate CountPulsesData_own(CountPulsesData) =
    shared_counter(?m, ?c) &*& CountPulsesData { counter: c, mutex: m, source: _ } == ?data;

predicate PrintCountData_own(PrintCountData) =
    shared_counter(?m, ?c) &*& PrintCountData { counter: c, mutex: m } == ?data;
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
predicate_ctor count_pulses_pre(CountPulsesData)() =
    CountPulsesData_own(?data);

lem_auto count_pulses_is_spawnee()
    req true;
    ens [_]is_Spawnee(count_pulses, count_pulses_pre);
{
    close count_pulses_pre(CountPulsesData { counter: _, mutex: _, source: _ })();
    leak count_pulses_pre(CountPulsesData { counter: _, mutex: _, source: _ })();
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
    //@ open shared_counter(mutex, counter);
    //@ assert [_]mutex_initialized(mutex);
    //@ assert exists(?v0, counter_cell(counter, v0));

    loop {
        //@ inv [_]mutex_initialized(mutex) &*& exists(?v, counter_cell(counter, v));
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);
        //@ open exists(?v1, counter_cell(counter, v1));
        //@ assert counter_cell(counter, v1);

        *counter = (*counter).checked_add(1).unwrap();

        //@ close counter_cell(counter, _);
        //@ close exists(_, counter_cell(counter, _));
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req shared_counter(mutex, counter);
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
predicate_ctor print_count_pre(PrintCountData)() =
    PrintCountData_own(?data);

lem_auto print_count_is_spawnee()
    req true;
    ens [_]is_Spawnee(print_count, print_count_pre);
{
    close print_count_pre(PrintCountData { counter: _, mutex: _ })();
    leak print_count_pre(PrintCountData { counter: _, mutex: _ })();
}
@*/

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ens true;
{
    let PrintCountData { counter, mutex } = data;
    //@ open PrintCountData_own(data);
    //@ open shared_counter(mutex, counter);
    //@ assert [_]mutex_initialized(mutex);
    //@ assert exists(?v0, counter_cell(counter, v0));

    loop {
        //@ inv [_]mutex_initialized(mutex) &*& exists(?v, counter_cell(counter, v));
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open exists(?v1, counter_cell(counter, v1));
        //@ assert counter_cell(counter, v1);

        print_u32(*counter);

        //@ close counter_cell(counter, _);
        //@ close exists(_, counter_cell(counter, _));
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req shared_counter(mutex, counter);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data);
    //@ print_count_is_spawnee();
    //@ close print_count_pre(data)();

    spawn(print_count, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        //@ close counter_cell(counter, 0u32);
        *counter = 0;

        let mutex = create_mutex();
        //@ close exists(0u32, counter_cell(counter, 0u32));
        //@ close shared_counter(mutex, counter);

        print_count_async(counter, mutex);

        loop {
            //@ inv [_]mutex_initialized(mutex) &*& exists(?v, counter_cell(counter, v));
            let source = wait_for_source();
            //@ close exists(_, counter_cell(counter, _));
            //@ close shared_counter(mutex, counter);
            count_pulses_async(counter, mutex, source);
        }
    }
}