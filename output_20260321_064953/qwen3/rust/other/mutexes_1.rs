//@ verifast_options{disable_ghost_blocks}

use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ pred sendable_own<T>(t: T) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req sendable_own(arg);
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

//@ pred mutex_own(mutex: *mut Mutex) = true;
//@ pred mutex_locked(guard: MutexGuard) = true;

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
//@ ens mutex_locked(result) &*& mutex_own(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_locked(guard);
//@ ens true;
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ens true;
{
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

//@ pred count_pulses_data_own(data: CountPulsesData) = 
//@     data.counter |-> ?c &*& 
//@     mutex_own(data.mutex) &*& 
//@     true;

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data_own(data);
//@ ens true;
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_locked(guard);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
        //@ close mutex_locked(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter |-> ?c &*& mutex_own(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data_own(data);
    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter |-> 0;

        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_locked(guard);
            let count = *counter;
            release(guard);
            //@ close mutex_locked(guard);
            print_u32(count);
        }
    }
}