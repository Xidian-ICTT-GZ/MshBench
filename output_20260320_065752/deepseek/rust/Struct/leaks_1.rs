#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

/*@
pred mutex_own(mutex: *mut Mutex) = 
    struct_Mutex_padding(&(*mutex)) &*& (*mutex).__lock.get() |-> ?lock &*& lock == 0 || lock == 1 &*&
    (*mutex).__queue |-> ?queue &*& queue == std::ptr::null_mut();
pred mutex(mutex: *mut Mutex) = 
    [_]alloc_block(mutex, std::mem::size_of::<Mutex>()) &*& mutex_own(mutex);
pred mutex_guard(guard: MutexGuard, mutex: *mut Mutex) = 
    (*mutex).__lock.get() |-> 1 &*& (*mutex).__queue |-> std::ptr::null_mut() &*&
    guard == guard;
@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
{
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close mutex_own(mutex);
    //@ close mutex(mutex);
    mutex.write(Mutex::new(()));
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

/*@
pred count_pulses_data(data: CountPulsesData) = 
    [_]alloc_block(data.counter, std::mem::size_of::<u32>()) &*&
    mutex(data.mutex) &*&
    data.source |-> _;
@*/

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex(mutex);
//@ ens mutex_guard(result, mutex);
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard) 
//@ req mutex_guard(_guard, ?mutex);
//@ ens mutex(mutex);
{}

unsafe fn wait_for_pulse(_source: i32) -> bool { true }
unsafe fn wait_for_source() -> i32 { 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data(data);
//@ ens true;
{
    //@ open count_pulses_data(data);
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        //@ inv mutex(mutex) &*& [_]alloc_block(counter, std::mem::size_of::<u32>());
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open mutex(mutex);
        //@ open mutex_own(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close mutex_own(mutex);
        //@ close mutex(mutex);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [_]alloc_block(counter, std::mem::size_of::<u32>()) &*& mutex(mutex);
//@ ens true;
{
    //@ close count_pulses_data(CountPulsesData { counter, mutex, source });
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@
pred print_count_data(data: PrintCountData) = 
    [_]alloc_block(data.counter, std::mem::size_of::<u32>()) &*&
    mutex(data.mutex);
@*/

unsafe fn print_count(data: PrintCountData)
//@ req print_count_data(data);
//@ ens true;
{
    //@ open print_count_data(data);
    let PrintCountData { counter, mutex } = data;
    loop {
        //@ inv mutex(mutex) &*& [_]alloc_block(counter, std::mem::size_of::<u32>());
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex(mutex);
        //@ open mutex_own(mutex);
        println!("{}", *counter);
        //@ close mutex_own(mutex);
        //@ close mutex(mutex);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req [_]alloc_block(counter, std::mem::size_of::<u32>()) &*& mutex(mutex);
//@ ens true;
{
    //@ close print_count_data(PrintCountData { counter, mutex });
    let data = PrintCountData { counter, mutex };
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close mutex_own(mutex);
        //@ close mutex(mutex);
        let mutex = create_mutex();
        
        print_count_async(counter, mutex);
        loop {
            //@ inv mutex(mutex) &*& [_]alloc_block(counter, std::mem::size_of::<u32>());
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}