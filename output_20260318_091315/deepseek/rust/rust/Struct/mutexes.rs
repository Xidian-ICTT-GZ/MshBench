use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ predicate mutex_handle(*mut Mutex) = true;
//@ predicate mutex_frac(*mut Mutex; f: real) = true;
//@ predicate mutex_guard(MutexGuard; *mut Mutex) = true;

//@ predicate_ctor Spawnee_pre<T>(unsafe fn(T) f, T arg)() = true;
//@ predicate is_Spawnee<T>(unsafe fn(T) f) = true;

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

//@ predicate counter_handle(*mut u32) = true;
//@ predicate counter_frac(*mut u32; f: real) = true;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_handle(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_frac(mutex, 1.0);
//@ ens mutex_guard(result, mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(guard, ?mutex);
//@ ens mutex_frac(mutex, 1.0);
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

//@ predicate count_pulses_data(CountPulsesData data) = 
//@     counter_frac(data.counter, 0.5) &*& mutex_frac(data.mutex, 0.5) &*& true;

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data(data);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;

    loop
    //@ inv counter_frac(counter, 0.5) &*& mutex_frac(mutex, 0.5);
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_frac(mutex, 0.5);
        //@ close mutex_frac(mutex, 0.5);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_frac(counter, 0.5) &*& mutex_frac(mutex, 0.5);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data(data);
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
        //@ close counter_handle(counter);
        //@ close counter_frac(counter, 0.5);
        //@ close counter_frac(counter, 0.5);
        
        let mutex = create_mutex();
        //@ close mutex_frac(mutex, 0.5);
        //@ close mutex_frac(mutex, 0.5);

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop
        //@ inv counter_handle(counter) &*& mutex_handle(mutex) &*& counter_frac(counter, 0.5) &*& mutex_frac(mutex, 0.5);
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter_frac(counter, 0.5);
            //@ close counter_frac(counter, 0.5);
            let count = *counter;
            release(guard);
            print_u32(count);
        }
    }
}