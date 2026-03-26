use std::alloc::{Layout, alloc, handle_alloc_error};

//@ predicate_ctor mutex_inv(counter: *mut u32)() = pointer(counter, ?c) &*& u32_(counter, c);
//@ predicate mutex_handle(mutex: *mut Mutex, counter: *mut u32) = [_]pointer(mutex, ?m) &*& [_]Mutex(m, mutex_inv(counter));
//@ predicate counter_handle(counter: *mut u32) = pointer(counter, ?c) &*& u32_(counter, c);

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
//@ ens result as usize != 0 &*& mutex_handle(result, _);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close mutex_inv(_)();
    //@ close exists(mutex_inv(_));
    mutex.write(Mutex::new(()));
    //@ close mutex_handle(mutex, _);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_handle(mutex, ?counter);
//@ ens mutex_handle(mutex, counter) &*& MutexGuard(result, mutex_inv(counter));
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req MutexGuard(guard, mutex_inv(?counter));
//@ ens mutex_handle(_, counter);
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
//@ req pointer(data.counter, ?c) &*& u32_(data.counter, c) &*& mutex_handle(data.mutex, data.counter);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    //@ close mutex_inv(counter)();
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_inv(counter)();
        //@ open u32_(counter, ?old);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close u32_(counter, old + 1);
        //@ close mutex_inv(counter)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_handle(counter) &*& mutex_handle(mutex, counter);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close exists(count_pulses);
    //@ close pointer(counter, ?c) &*& u32_(counter, c) &*& mutex_handle(mutex, counter);
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
        //@ close u32_(counter, 0);
        //@ close counter_handle(counter);
        
        let mutex = create_mutex();
        //@ open mutex_handle(mutex, ?c);
        //@ assert c == counter;
        //@ close mutex_handle(mutex, counter);

        //@ split_fraction counter_handle(counter) as _, _;
        //@ split_fraction mutex_handle(mutex, counter) as _, _;
        count_pulses_async(counter, mutex, 1);
        //@ split_fraction counter_handle(counter) as _, _;
        //@ split_fraction mutex_handle(mutex, counter) as _, _;
        count_pulses_async(counter, mutex, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_inv(counter)();
            let count = *counter;
            //@ close mutex_inv(counter)();
            release(guard);
            print_u32(count);
        }
    }
}