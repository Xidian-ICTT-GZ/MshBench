#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@

pred u32_ptr(p: *mut u32; v: u32) =
    std::alloc::alloc_block(p as *mut u8, Layout::new::<u32>()) &*& *(p) |-> v;

pred mutex_ptr(p: *mut Mutex) =
    std::alloc::alloc_block(p as *mut u8, Layout::new::<Mutex>()) &*& struct_Mutex_padding(p) &*& std::sync::Mutex_(p, ());

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

//@ req true;
//@ ens mutex_ptr(result);
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close struct_Mutex_padding(mutex);
    //@ close std::sync::Mutex_(mutex, ());
    mutex.write(Mutex::new(()));
    //@ close mutex_ptr(mutex);
    mutex
}

//@ req mutex_ptr(mutex);
//@ ens mutex_ptr(mutex);
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    //@ open mutex_ptr(mutex);
    let g = (*mutex).lock().unwrap();
    //@ close mutex_ptr(mutex);
    g
}

//@ req true;
//@ ens true;
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
}

//@ req true;
//@ ens true;
unsafe fn wait_for_source() -> i32
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

//@ req true;
//@ ens true;
unsafe fn wait_for_pulse(_source: i32) -> bool
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

//@ req true;
//@ ens true;
//@ assume_correct
unsafe fn print_u32(n: u32)
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ req true;
//@ ens true;
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ inv true;
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

//@ req true;
//@ ens true;
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    let data = CountPulsesData { counter, mutex, source };

    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

//@ req true;
//@ ens true;
unsafe fn print_count(data: PrintCountData)
{
    let PrintCountData {counter, mutex} = data;
    loop {
        //@ inv true;
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);

        print_u32(*counter);

        release(guard);
    }
}

//@ req true;
//@ ens true;
unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
{
    let data = PrintCountData { counter, mutex };

    spawn(print_count, data);
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        print_count_async(counter, mutex);

        loop {
            //@ inv true;
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}