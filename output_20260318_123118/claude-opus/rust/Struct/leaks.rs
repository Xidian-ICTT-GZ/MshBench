#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

predicate mutex(Mutex *mutex) = mutex |-> _;

predicate mutex_guard(MutexGuard guard, Mutex *mutex) = true;

predicate u32_cell(u32 *p, u32 v) = p |-> v;

predicate count_pulses_data(struct CountPulsesData data; u32 *counter, Mutex *mutex, int source) =
    data.counter |-> counter &*& data.mutex |-> mutex &*& data.source |-> source;

predicate print_count_data(struct PrintCountData data; u32 *counter, Mutex *mutex) =
    data.counter |-> counter &*& data.mutex |-> mutex;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
    //@ requires [_]is_Spawnee(f, ?pre) &*& pre(arg);
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
    //@ requires true;
    //@ ensures mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex(mutex);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
    //@ requires mutex(mutex);
    //@ ensures mutex_guard(result, mutex) &*& mutex(mutex);
{
    let guard = (*mutex).lock().unwrap();
    //@ close mutex_guard(guard, mutex);
    guard
}

unsafe fn release(guard: MutexGuard)
    //@ requires mutex_guard(guard, ?mutex);
    //@ ensures mutex(mutex);
{
    drop(guard);
    //@ open mutex_guard(guard, mutex);
}

unsafe fn wait_for_source() -> i32
    //@ requires true;
    //@ ensures result == 42;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
    //@ requires true;
    //@ ensures result == false || result == true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
    //@ requires true;
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
    //@ requires count_pulses_data(data, ?counter, ?mutex, ?source) &*& u32_cell(counter, ?v) &*& mutex(mutex);
    //@ ensures count_pulses_data(data, counter, mutex, source) &*& u32_cell(counter, ?v2) &*& mutex(mutex) &*& v2 >= v;
{
    let CountPulsesData {counter, mutex, source} = data;

    //@ open count_pulses_data(data, counter, mutex, source);
    while (true)
        //@ invariant count_pulses_data(data, counter, mutex, source) &*& u32_cell(counter, ?cv) &*& mutex(mutex);
    {
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);

        let old_v = *counter;
        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
        //@ assert u32_cell(counter, ?new_v);
        //@ assert new_v == old_v + 1;
    }
    //@ close count_pulses_data(data, counter, mutex, source);
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
    //@ requires u32_cell(counter, _) &*& mutex(mutex);
    //@ ensures true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data(data, counter, mutex, source);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
    //@ requires print_count_data(data, ?counter, ?mutex) &*& u32_cell(counter, _) &*& mutex(mutex);
    //@ ensures print_count_data(data, counter, mutex) &*& u32_cell(counter, _) &*& mutex(mutex);
{
    let PrintCountData {counter, mutex} = data;
    //@ open print_count_data(data, counter, mutex);
    while (true)
        //@ invariant print_count_data(data, counter, mutex) &*& u32_cell(counter, _) &*& mutex(mutex);
    {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        print_u32(*counter);
        release(guard);
    }
    //@ close print_count_data(data, counter, mutex);
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
    //@ requires u32_cell(counter, _) &*& mutex(mutex);
    //@ ensures true;
{
    let data = PrintCountData { counter, mutex };
    //@ close print_count_data(data, counter, mutex);
    spawn(print_count, data);
}

fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close u32_cell(counter, 0);

        let mutex = create_mutex();

        print_count_async(counter, mutex);

        while (true)
            //@ invariant u32_cell(counter, _) &*& mutex(mutex);
        {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}