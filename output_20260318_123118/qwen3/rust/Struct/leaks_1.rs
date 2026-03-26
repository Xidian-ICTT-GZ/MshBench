#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};
use std::thread;
use std::time::Duration;

predicate_ctor is_Spawnee<T>(unsafe fn(T) -> (), predicate(T))();

predicate u32_ptr(*mut u32; u32) = *0..4 |-> ?val &*& val == _;

predicate mutex_ptr(*mut Mutex; ) = *0.._ |-> _;

predicate CountPulsesData_full(CountPulsesData; *mut u32, *mut Mutex, i32) =
    u32_ptr(?counter, ?val) &*& mutex_ptr(?mutex, ) &*&
    struct_CountPulsesData_padding(?counter, ?mutex, ?source) &*&
    counter == counter &*& mutex == mutex &*& source == source;

predicate PrintCountData_full(PrintCountData; *mut u32, *mut Mutex) =
    u32_ptr(?counter, ?val) &*& mutex_ptr(?mutex, ) &*&
    struct_PrintCountData_padding(?counter, ?mutex) &*&
    counter == counter &*& mutex == mutex;

lemma void struct_CountPulsesData_padding(*mut u32 counter, *mut Mutex mutex, i32 source)() req true; ens true {}
lemma void struct_PrintCountData_padding(*mut u32 counter, *mut Mutex mutex)() req true; ens true {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
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
//@ ens mutex_ptr(result, );
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_ptr(mutex, );
//@ ens mutex_ptr(mutex, ) &*& [_]mutex_locked(mutex);
{
    (&*mutex).lock().unwrap()
}
unsafe fn release(_guard: MutexGuard)
//@ req [_]mutex_locked(?mutex) &*& mutex_ptr(mutex, );
//@ ens mutex_ptr(mutex, );
{}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{ true }
unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{ 1 }

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_full(data, ?counter, ?mutex, ?source) &*& u32_ptr(counter, ?val);
//@ ens false;
{
    
    let CountPulsesData { counter, mutex, source } = data;
    loop
    //@ invariant u32_ptr(counter, ?v) &*& mutex_ptr(mutex, ) &*& source == source;
    {
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
    //@ leak u32_ptr(counter, _);
    //@ leak mutex_ptr(mutex, );
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req u32_ptr(counter, ?val) &*& mutex_ptr(mutex, );
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    
    
    spawn(count_pulses, data);
    //@ close CountPulsesData_full(data, counter, mutex, source);
    //@ close_u32_ptr(counter, val);
    //@ close_mutex_ptr(mutex, );
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_full(data, ?counter, ?mutex) &*& u32_ptr(counter, ?val);
//@ ens false;
{
    
    let PrintCountData { counter, mutex } = data;
    loop
    //@ invariant u32_ptr(counter, ?v) &*& mutex_ptr(mutex, );
    {
        
        thread::sleep(Duration::from_millis(1000));
        let guard = acquire(mutex);
        
        println!("{}", *counter);
        
        release(guard);
    }
    //@ leak u32_ptr(counter, _);
    //@ leak mutex_ptr(mutex, );
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req u32_ptr(counter, ?val) &*& mutex_ptr(mutex, );
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    
    
    spawn(print_count, data);
    //@ close PrintCountData_full(data, counter, mutex);
    //@ close_u32_ptr(counter, val);
    //@ close_mutex_ptr(mutex, );
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close u32_ptr(counter, 0);
        
        
        let mutex = create_mutex();
        //@ close mutex_ptr(mutex, );
        
        print_count_async(counter, mutex);
        loop
        //@ invariant u32_ptr(counter, ?v) &*& mutex_ptr(mutex, );
        {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}