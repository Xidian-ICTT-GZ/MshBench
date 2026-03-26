use std::alloc::{Layout, alloc, handle_alloc_error};

/*@

pred Mutex(mutex: *mut Mutex; P: pred());

pred Mutex_held(mutex: *mut Mutex, guard: MutexGuard, P: pred());

pred counter_inv(counter: *mut u32)() =
    (*counter) |-> ?v;

pred_ctor counting_frac(mutex: *mut Mutex, counter: *mut u32)(;) =
    [1/2]Mutex(mutex, counter_inv(counter));

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req is_thread_run_func(f, ?pre, T) &*& pre(arg);
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
//@ req exists::<pred()>(?P) &*& P();
//@ ens Mutex(result, P);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close Mutex(mutex, P);
    mutex
}
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?q]Mutex(mutex, ?P);
//@ ens Mutex_held(mutex, result, P) &*& P() &*& [q]Mutex(mutex, P);
{
    let guard = (*mutex).lock().unwrap();
    //@ open [q]Mutex(mutex, P);
    //@ close Mutex_held(mutex, guard, P);
    //@ close [q]Mutex(mutex, P);
    guard
}
unsafe fn release(guard: MutexGuard)
//@ req Mutex_held(?mutex, guard, ?P) &*& P();
//@ ens true;
{
    //@ open Mutex_held(mutex, guard, P);
    drop(guard);
}
unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ens true;
{
    //@ leak true;

    std::thread::sleep(std::time::Duration::from_millis(500));
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

pred count_pulses_pre(data: CountPulsesData) =
    counting_frac(data.mutex, data.counter)();

pred_ctor is_thread_run_func<T>(f: unsafe fn(T), pre: pred(T), T_unused: T)(;) = true;

@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_pre(data);
//@ ens false;
{
    //@ open count_pulses_pre(data);
    //@ open counting_frac(data.mutex, data.counter)();
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ inv [1/2]Mutex(mutex, counter_inv(counter));
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_inv(counter)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_inv(counter)();
        release(guard);
    }
}
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counting_frac(mutex, counter)();
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_pre(data);
    //@ close is_thread_run_func(count_pulses, count_pulses_pre, data)();
    //@ close exists(is_thread_run_func(count_pulses, count_pulses_pre, data));
    spawn(count_pulses, data);
}
fn main()
//@ req true;
//@ ens false;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;

        //@ close counter_inv(counter)();
        //@ close exists(counter_inv(counter));
        let mutex = create_mutex();
        //@ close counting_frac(mutex, counter)();
        count_pulses_async(counter, mutex, 1);
        //@ close counting_frac(mutex, counter)();
        count_pulses_async(counter, mutex, 2);
        loop {
            //@ inv Mutex(mutex, counter_inv(counter));
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter_inv(counter)();
            let count = *counter;
            //@ close counter_inv(counter)();
            release(guard);
            print_u32(count);
        }
    }
}