#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@
pred mutex_own(m: *mut Mutex) = alloc_block(m, std::mem::size_of::<Mutex>()) &*& struct_Mutex_padding(m);
pred mutex_guard_own(g: MutexGuard) = true;
@*/

/*@
pred counter_own(c: *mut u32) = alloc_block(c, std::mem::size_of::<u32>()) &*& u32__own(c, _);
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
//@ ens mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex);
//@ ens mutex_own(mutex) &*& mutex_guard_own(result);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard_own(guard);
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
pred count_pulses_data_own(data: CountPulsesData) = 
    counter_own(data.counter) &*& mutex_own(data.mutex) &*& true;
@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data_own(data);
//@ ens true;
{
    let CountPulsesData {counter, mutex, source} = data;
    //@ open count_pulses_data_own(_);
    
    loop {
        //@ inv counter_own(counter) &*& mutex_own(mutex);
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open mutex_own(mutex);
        //@ open counter_own(counter);
        //@ open u32__own(counter, ?v);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close u32__own(counter, v+1);
        //@ close counter_own(counter);
        //@ close mutex_own(mutex);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_own(counter) &*& mutex_own(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data_own(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@
pred print_count_data_own(data: PrintCountData) = 
    counter_own(data.counter) &*& mutex_own(data.mutex);
@*/

unsafe fn print_count(data: PrintCountData)
//@ req print_count_data_own(data);
//@ ens true;
{
    let PrintCountData {counter, mutex} = data;
    //@ open print_count_data_own(_);
    
    loop {
        //@ inv counter_own(counter) &*& mutex_own(mutex);
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex_own(mutex);
        //@ open counter_own(counter);
        //@ open u32__own(counter, ?v);
        print_u32(*counter);
        //@ close u32__own(counter, v);
        //@ close counter_own(counter);
        //@ close mutex_own(mutex);
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_own(counter) &*& mutex_own(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close print_count_data_own(data);
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
        //@ close u32__own(counter, 0);
        //@ close counter_own(counter);
        
        let mutex = create_mutex();
        
        print_count_async(counter, mutex);

        loop {
            //@ inv counter_own(counter) &*& mutex_own(mutex);
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}