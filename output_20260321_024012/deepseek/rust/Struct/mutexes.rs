use std::alloc::{Layout, alloc, handle_alloc_error};

//@ predicate mutex_invariant(?mu, ?frac, ?inner_pred) = true; // Placeholder
//@ predicate mutex_frac(?mu, ?frac) = true; // Placeholder
//@ predicate_ctor Spawnee_pre<T>(unsafe fn(T) f, T arg)() = true; // Placeholder
//@ predicate is_Spawnee<T>(unsafe fn(T) f, predicate() pre) = true; // Placeholder

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
//@ ens result as usize != 0 &*& mutex_frac(result, 1) &*& mutex_invariant(result, 1, true);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_frac(mutex, 1) &*& mutex_invariant(mutex, 1, ?inner_pred);
//@ ens mutex_frac(mutex, 1) &*& mutex_invariant(mutex, 1, inner_pred) &*& inner_pred();
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
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

unsafe fn count_pulses(data: CountPulsesData)
//@ req data.counter as usize != 0 &*& data.mutex as usize != 0 &*& mutex_frac(data.mutex, 1) &*& mutex_invariant(data.mutex, 1, ?inner_pred) &*& inner_pred() &*& pointer(data.counter, ?count_val);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_invariant(mutex, 1, inner_pred)();
        //@ open inner_pred();
        //@ open pointer(counter, ?old_val);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close pointer(counter, old_val + 1);
        //@ close inner_pred();
        //@ close mutex_invariant(mutex, 1, inner_pred)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter as usize != 0 &*& mutex as usize != 0 &*& mutex_frac(mutex, 1) &*& mutex_invariant(mutex, 1, ?inner_pred) &*& inner_pred() &*& pointer(counter, ?count_val);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close Spawnee_pre(count_pulses, data)();
    //@ close is_Spawnee(count_pulses, Spawnee_pre(count_pulses, data));
    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        //@ close pointer(counter, 0);
        *counter = 0;
        let mutex = create_mutex();
        //@ close mutex_invariant(mutex, 1, true)();
        //@ close pointer(counter, 0);
        count_pulses_async(counter, mutex, 1);
        //@ close pointer(counter, 0);
        count_pulses_async(counter, mutex, 2);
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_invariant(mutex, 1, true)();
            //@ open true();
            let count = *counter;
            //@ close true();
            //@ close mutex_invariant(mutex, 1, true)();
            release(guard);
            print_u32(count);
        }
    }
}