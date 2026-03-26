use std::alloc::{Layout, alloc, handle_alloc_error};

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

/*#

predicate mutex_pointer(void* p) = true;

predicate counter_pointer(void* p, int v) = p |-> v;

#*/

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ensures mutex_pointer(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_pointer(mutex);
//@ ensures true;
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
//@ ensures true;
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ensures true;
{
    
    
    std::thread::sleep(std::time::Duration::from_millis(500)); 
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req mutex_pointer(data.mutex) &*& counter_pointer(data.counter, ?v);
//@ ensures true;
{
    
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        
        wait_for_pulse(source);
        let guard = acquire(mutex);
        
        //@ open counter_pointer(counter, ?c);
        let new_val = (*counter).checked_add(1).unwrap();
        *counter = new_val;
        //@ close counter_pointer(counter, new_val);
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req mutex_pointer(mutex) &*& counter_pointer(counter, _);
//@ ensures true;
{
    let data = CountPulsesData { counter, mutex, source };
    
    
    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ensures true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        
        //@ close counter_pointer(counter, 0);
        
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            
            //@ open counter_pointer(counter, ?count);
            let count = *counter;
            //@ close counter_pointer(counter, count);
            
            release(guard);
            print_u32(count);
        }
    }
}