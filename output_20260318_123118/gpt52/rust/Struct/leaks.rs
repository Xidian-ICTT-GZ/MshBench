#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

//@ predicate u32_counter(ptr: *mut u32, v: u32) = ptr as usize != 0 &*& *ptr |-> v;

//@ predicate mutex_raw(ptr: *mut Mutex) = ptr as usize != 0 &*& std::sync::Mutex_state(ptr, ());
//@ predicate mutex_share(ptr: *mut Mutex) = ptr as usize != 0 &*& [_]std::sync::Mutex_share(ptr, ());

//@ predicate counter_mutex_invariant(counter: *mut u32, mutex: *mut Mutex) =
//@     u32_counter(counter, ?v) &*& mutex_share(mutex);

//@ predicate CountPulsesData_own(d: CountPulsesData) =
//@     counter_mutex_invariant(d.counter, d.mutex);

//@ predicate PrintCountData_own(d: PrintCountData) =
//@     counter_mutex_invariant(d.counter, d.mutex);

//@ predicate SpawnToken() = std::thread::SpawnToken();

//@ lemma void spawn_token_create()
//@     requires true;
//@     ensures SpawnToken();
//@ { std::thread::spawn_token_create(); }

//@ lemma void spawn_token_consume()
//@     requires SpawnToken();
//@     ensures true;
//@ { std::thread::spawn_token_consume(); }

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req SpawnToken() &*& [_]is_Spawnee(f, ?pre) &*& pre(arg);
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
//@ ens mutex_raw(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_raw(mutex);
//@ ens std::sync::Mutex_guard(result, mutex, (), ());
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req std::sync::Mutex_guard(guard, ?mutex, (), ());
//@ ens mutex_raw(mutex);
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

//@ predicate_ctor count_pulses_pre(data: CountPulsesData)() = CountPulsesData_own(data);

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data);
//@ ens false;
{
    
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ invariant counter_mutex_invariant(counter, mutex);
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open std::sync::Mutex_guard(guard, mutex, (), ());
        //@ open counter_mutex_invariant(counter, mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        //@ close counter_mutex_invariant(counter, mutex);
        //@ close std::sync::Mutex_guard(guard, mutex, (), ());
        release(guard);
    }
    //@ leak counter_mutex_invariant(counter, mutex);
    //@ assert false;
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req SpawnToken() &*& counter_mutex_invariant(counter, mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    
    
    //@ close CountPulsesData_own(data);
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

//@ predicate_ctor print_count_pre(data: PrintCountData)() = PrintCountData_own(data);

unsafe fn print_count(data: PrintCountData)
//@ req PrintCountData_own(data);
//@ ens false;
{
    
    let PrintCountData {counter, mutex} = data;
    loop {
        //@ invariant counter_mutex_invariant(counter, mutex);
        
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open std::sync::Mutex_guard(guard, mutex, (), ());
        //@ open counter_mutex_invariant(counter, mutex);
        
        print_u32(*counter);
        
        //@ close counter_mutex_invariant(counter, mutex);
        //@ close std::sync::Mutex_guard(guard, mutex, (), ());
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req SpawnToken() &*& counter_mutex_invariant(counter, mutex);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    
    
    //@ close PrintCountData_own(data);
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
        //@ close u32_counter(counter, 0);
        *counter = 0;
        
        
        let mutex = create_mutex();
        //@ leak mutex_raw(mutex);
        //@ close mutex_share(mutex);
        //@ close counter_mutex_invariant(counter, mutex);
        
        spawn_token_create();
        print_count_async(counter, mutex);

        loop {
            //@ invariant counter_mutex_invariant(counter, mutex);
            
            let source = wait_for_source();
            spawn_token_create();
            count_pulses_async(counter, mutex, source);
        }
    }
}