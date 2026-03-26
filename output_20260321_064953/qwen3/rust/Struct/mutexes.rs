use std::alloc::{Layout, alloc, handle_alloc_error};

//@ pred is_Spawnee<T>(unsafe fn(T), pred(T)) = true;

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

//@ pred mutex_own(mutex: *mut Mutex) = true;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_own(mutex);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex);
//@ ens mutex_own(mutex);
{
    //@ open mutex_own(mutex);
    let guard = (*mutex).lock().unwrap();
    //@ close mutex_own(mutex);
    guard
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

//@ pred counter_own(counter: *mut u32) = true;

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_own(data.counter) &*& mutex_own(data.mutex);
//@ ens true;
{
    
    let CountPulsesData {counter, mutex, source} = data;
    //@ open counter_own(counter);
    //@ open mutex_own(mutex);

    loop {
        
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_own(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
        //@ close mutex_own(mutex);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_own(counter) &*& mutex_own(mutex);
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
        //@ close counter_own(counter);
        
        
        let mutex = create_mutex();
        //@ assert mutex_own(mutex);

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_own(mutex);
            
            let count = *counter;
            
            release(guard);
            //@ close mutex_own(mutex);
            print_u32(count);
        }
    }
}