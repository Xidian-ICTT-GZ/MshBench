#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

predicate is_Spawnee<T>(unsafe fn(T), predicate(T)) = true;

predicate u32_own(*mut u32; u32) = *0.. => u32;

predicate mutex_own(*mut Mutex) = *0.. => Mutex(());

predicate CountPulsesData_full(CountPulsesData; *mut u32, *mut Mutex, i32) =
    u32_own(?counter, ?n) &*& mutex_own(?mutex) &*& counter == counter &*& mutex == mutex &*& source == source;

predicate PrintCountData_full(PrintCountData; *mut u32, *mut Mutex) =
    u32_own(?counter, ?n) &*& mutex_own(?mutex) &*& counter == counter &*& mutex == mutex;

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
//@ ens mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex);
//@ ens mutex_guard(mutex, _);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(?mutex, _);
//@ ens mutex_own(mutex);
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
//@ req CountPulsesData_full(data, ?counter, ?mutex, ?source) &*& u32_own(counter, ?n);
//@ ens u32_own(counter, _);
{
    
    let CountPulsesData {counter, mutex, source} = data;

    loop
    //@ inv u32_own(counter, ?m) &*& mutex_own(mutex) &*& source == source;
    {
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req u32_own(counter, ?n) &*& mutex_own(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    
    
    spawn(count_pulses, data);
    //@ close CountPulsesData_full(data, counter, mutex, source);
    //@ leak CountPulsesData_full(data, counter, mutex, source) &*& u32_own(counter, _);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_full(data, ?counter, ?mutex) &*& u32_own(counter, ?n);
//@ ens u32_own(counter, _);
{
    
    let PrintCountData {counter, mutex} = data;
    loop
    //@ inv u32_own(counter, ?m) &*& mutex_own(mutex);
    {
        
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        
        print_u32(*counter);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req u32_own(counter, ?n) &*& mutex_own(mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    
    
    spawn(print_count, data);
    //@ close PrintCountData_full(data, counter, mutex);
    //@ leak PrintCountData_full(data, counter, mutex) &*& u32_own(counter, _);
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
        //@ close u32_own(counter, 0);
        
        
        let mutex = create_mutex();
        //@ assert mutex_own(mutex);

        print_count_async(counter, mutex);
        //@ open u32_own(counter, _); open mutex_own(mutex);

        loop
        //@ inv true;
        {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
            //@ open u32_own(counter, _); open mutex_own(mutex);
        }
    }
}