#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
pred_ctor mutex_inv(counter: *mut u32)() = (*counter) |-> _;

pred counter_shared(counter: *mut u32, mutex: *mut Mutex) =
    [1/2](*mutex) |-> _ &*& [1/2]Mutex_share(mutex, mutex_inv(counter));

pred CountPulsesData_own(data: CountPulsesData) =
    data.counter |-> ?counter &*& data.mutex |-> ?mutex &*& data.source |-> _ &*&
    counter_shared(counter, mutex);

pred PrintCountData_own(data: PrintCountData) =
    data.counter |-> ?counter &*& data.mutex |-> ?mutex &*&
    counter_shared(counter, mutex);
@*/

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
//@ req (*?counter) |-> _;
//@ ens (*result) |-> _ &*& Mutex_share(result, mutex_inv(counter));
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    //@ close mutex_inv(counter)();
    //@ create_Mutex_share(mutex, mutex_inv(counter));
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f](*mutex) |-> _ &*& [f]Mutex_share(mutex, ?inv);
//@ ens [f](*mutex) |-> _ &*& [f]Mutex_share(mutex, inv) &*& Mutex_guard(result, inv) &*& inv();
{
    //@ open_Mutex_share(mutex);
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req Mutex_guard(guard, ?inv) &*& inv();
//@ ens true;
{
    //@ close_Mutex_share(guard);
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
lem count_pulses_is_Spawnee()
    req true;
    ens [_]is_Spawnee(count_pulses, CountPulsesData_own);
{
    produce_fn_ptr_chunk Spawnee(count_pulses)(CountPulsesData_own)(data) { call(); }
}
@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data);
//@ ens true;
{
    //@ open CountPulsesData_own(data);
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;
    //@ open counter_shared(counter, mutex);

    loop
    //@ inv [1/2](*mutex) |-> _ &*& [1/2]Mutex_share(mutex, mutex_inv(counter));
    {
        let done = wait_for_pulse(source);
        if done {
            break;
        }
        let guard = acquire(mutex);
        //@ open mutex_inv(counter)();

        *counter = (*counter).checked_add(1).unwrap();

        //@ close mutex_inv(counter)();
        release(guard);
    }
    //@ leak (*mutex) |-> _;
    //@ leak Mutex_share(mutex, mutex_inv(counter));
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_shared(counter, mutex);
//@ ens true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    //@ close CountPulsesData_own(data);
    //@ count_pulses_is_Spawnee();
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@
lem print_count_is_Spawnee()
    req true;
    ens [_]is_Spawnee(print_count, PrintCountData_own);
{
    produce_fn_ptr_chunk Spawnee(print_count)(PrintCountData_own)(data) { call(); }
}
@*/

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ens true;
{
    //@ open PrintCountData_own(data);
    let PrintCountData { counter, mutex } = data;
    //@ open counter_shared(counter, mutex);
    loop
    //@ inv [1/2](*mutex) |-> _ &*& [1/2]Mutex_share(mutex, mutex_inv(counter));
    {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex_inv(counter)();

        print_u32(*counter);

        //@ close mutex_inv(counter)();
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_shared(counter, mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close PrintCountData_own(data);
    //@ print_count_is_Spawnee();
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