use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ predicate mutex_handle(*mut Mutex) = true;
//@ predicate mutex_frac(*mut Mutex; f) = true;
//@ predicate mutex_guard(MutexGuard) = true;

//@ predicate_ctor Spawnee_pre<T>(unsafe fn(arg: T) -> (), arg)() = true;

//@ predicate is_Spawnee<T>(unsafe fn(arg: T) -> (), predicate_ctor(Spawnee_pre<T>)) = true;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg)();
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

//@ predicate mutex_frac(*mut Mutex; f) = 
//@     struct_Mutex_padding(?m) &*& 
//@     [_]m.lock |-> ?lock_func &*& 
//@     [_]m.data |-> ?inner &*& 
//@     inner == () &*& 
//@     f == 1;

//@ predicate mutex_handle(*mut Mutex) = 
//@     mutex_frac(?mutex_ptr; 1) &*& mutex_ptr == mutex_ptr;

//@ predicate mutex_guard(MutexGuard) = true;

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
//@ req mutex_frac(mutex; 1);
//@ ens mutex_guard(result) &*& mutex_frac(mutex; 1);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(guard);
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

//@ predicate count_pulses_data(CountPulsesData data) = 
//@     data.counter |-> ?counter_ptr &*& 
//@     counter_ptr != 0 &*& 
//@     integer(counter_ptr, ?counter_val) &*& 
//@     data.mutex |-> ?mutex_ptr &*& 
//@     mutex_frac(mutex_ptr; 1) &*& 
//@     data.source |-> ?src &*& 
//@     src == src;

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data(data);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

//@ predicate_ctor count_pulses_pre(CountPulsesData data)() = 
//@     count_pulses_data(data);

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req integer(counter, ?counter_val) &*& counter != 0 &*& mutex_frac(mutex; 1);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_pre(data)();
    //@ close exists(predicate_ctor(count_pulses_pre));
    //@ close is_Spawnee(count_pulses, count_pulses_pre);
    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ens false;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close integer(counter, 0);
        
        let mutex = create_mutex();
        //@ close mutex_frac(mutex, 1);
        
        //@ close integer(counter, 0);
        //@ close mutex_frac(mutex, 1);
        count_pulses_async(counter, mutex, 1);
        
        //@ close integer(counter, _);
        //@ close mutex_frac(mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            //@ close mutex_frac(mutex, 1);
            let guard = acquire(mutex);
            let count = *counter;
            release(guard);
            print_u32(count);
        }
    }
}