#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@

predicate alloc_block_counter(void* p, uint32_t value) =
    p |-> value&*& malloc_block(p, sizeof(uint32_t));

predicate alloc_block_mutex(void* p) = 
    p |-> _ &*& malloc_block(p, sizeof(std::sync::Mutex<()>));

predicate counter_mutex_shared(CountPulsesData data, uint32_t value) = 
    alloc_block_counter(data.counter, value) &*& alloc_block_mutex(data.mutex);

predicate counter_mutex_print(PrintCountData data, uint32_t value) =
    alloc_block_counter(data.counter, value) &*& alloc_block_mutex(data.mutex);

fixpoint bool is_Spawnee_impl(unsafe fn(arg: CountPulsesData) f, CountPulsesData arg) { true }
fixpoint bool is_Spawnee_impl_print(unsafe fn(arg: PrintCountData) f, PrintCountData arg) { true }

predicate is_Spawnee(unsafe fn(arg: CountPulsesData) f, predicate<CountPulsesData> pre) = 
    // For simplicity, pre means we own counter & mutex.
    true;

predicate is_Spawnee_print(unsafe fn(arg: PrintCountData) f, predicate<PrintCountData> pre) = 
    true;

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

//@ req true;
//@ ensures alloc_block_mutex(result as *mut _);
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

//@ req alloc_block_mutex(mutex);
//@ ensures true;
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (&*mutex).lock().unwrap()
}
//@ req true;
//@ ensures true;
unsafe fn release(_guard: MutexGuard) {}

//@ req true;
//@ ensures true;
unsafe fn wait_for_pulse(_source: i32) -> bool { true }
//@ req true;
//@ ensures true;
unsafe fn wait_for_source() -> i32 { 1 }

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ req alloc_block_counter(data.counter, ?v) &*& alloc_block_mutex(data.mutex);
//@ ensures true;
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData { counter, mutex, source } = data;

    //@ open alloc_block_counter(counter, ?v);
    //@ open alloc_block_mutex(mutex);
    loop {
        //@ inv alloc_block_counter(counter, ?v) &*& alloc_block_mutex(mutex);

        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);

        //@ open alloc_block_counter(counter, v);
        let curr = *counter;
        //@ assert *counter == v;
        let new_v = curr.checked_add(1).unwrap();

        *counter = new_v;
        //@ close alloc_block_counter(counter, new_v);

        release(guard);
        //@ close alloc_block_mutex(mutex);
    }
    //@ close alloc_block_counter(counter, _);
    //@ close alloc_block_mutex(mutex);
}

//@ req alloc_block_counter(counter, ?v) &*& alloc_block_mutex(mutex);
//@ ensures true;
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    let data = CountPulsesData { counter, mutex, source };

    //@ close is_Spawnee(count_pulses, ?pre);
    //@ close pre(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

//@ req alloc_block_counter(data.counter, ?v) &*& alloc_block_mutex(data.mutex);
//@ ensures true;
unsafe fn print_count(data: PrintCountData)
{
    let PrintCountData { counter, mutex } = data;

    //@ open alloc_block_counter(counter, ?v);
    //@ open alloc_block_mutex(mutex);
    loop {
        //@ inv alloc_block_counter(counter, ?v) &*& alloc_block_mutex(mutex);

        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);

        //@ open alloc_block_counter(counter, v);
        println!("{}", *counter);
        //@ close alloc_block_counter(counter, v);

        release(guard);
        //@ close alloc_block_mutex(mutex);
    }
    //@ close alloc_block_counter(counter, _);
    //@ close alloc_block_mutex(mutex);
}

//@ req alloc_block_counter(counter, ?v) &*& alloc_block_mutex(mutex);
//@ ensures true;
unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
{
    let data = PrintCountData { counter, mutex };

    //@ close is_Spawnee(print_count, ?pre_p);
    //@ close pre_p(data);
    spawn(print_count, data);
}

//@ requires true;
//@ ensures true;
fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;

        //@ close alloc_block_counter(counter, 0);

        let mutex = create_mutex();

        //@ close alloc_block_mutex(mutex);

        print_count_async(counter, mutex);
        loop {
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}