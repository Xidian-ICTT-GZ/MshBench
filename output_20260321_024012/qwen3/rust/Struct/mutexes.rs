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

//@ pred mutex_own(*mut Mutex) = true;

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

//@ pred counter_own(*mut u32, u32) = true;

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req counter_own(data.counter, ?c) &*& mutex_own(data.mutex);
//@ ens counter_own(data.counter, _) &*& mutex_own(data.mutex);
{
    
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_own(counter, _);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_own(counter, *counter);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_own(counter, ?c) &*& mutex_own(mutex);
//@ ens counter_own(counter, c) &*& mutex_own(mutex);
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
        //@ close counter_own(counter, 0);
        
        
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter_own(counter, _);
            let count = *counter;
            //@ close counter_own(counter, count);
            release(guard);
            print_u32(count);
        }
    }
}