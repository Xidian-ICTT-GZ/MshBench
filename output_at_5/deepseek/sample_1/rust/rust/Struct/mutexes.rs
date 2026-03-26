use std::alloc::{Layout, alloc, handle_alloc_error};

//@ predicate_ctor mutex_inv(counter: *mut u32)() = atomic_mask(1) &*& pointer(counter, ?v) &*& v as u32 == v;

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
//@ ens pointer(result, _);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req pointer(mutex, ?m) &*& [_]mutex(m, ?inv);
//@ ens pointer(mutex, m) &*& mutex_guard(m, inv, currentThread, ?p) &*& p();
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(?m, ?inv, currentThread, ?p) &*& p();
//@ ens [_]mutex(m, inv);
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
//@ req pointer(data.counter, ?c) &*& pointer(data.mutex, ?m) &*& [_]mutex(m, mutex_inv(data.counter));
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_inv(counter)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close mutex_inv(counter)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req pointer(counter, ?c) &*& pointer(mutex, ?m) &*& [_]mutex(m, mutex_inv(counter));
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
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
        let mutex = create_mutex();
        //@ close mutex_inv(counter)();
        //@ close exists(mutex_inv(counter));
        //@ leak exists(_);
        count_pulses_async(counter, mutex, 1);
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