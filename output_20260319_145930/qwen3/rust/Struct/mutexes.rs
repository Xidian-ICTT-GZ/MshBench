//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error};

/*@ pred CountPulsesData_pred(CountPulsesData counter, *mut u32 c, *mut Mutex m, i32 s) =
    counter == CountPulsesData { counter: c, mutex: m, source: s };
@*/

/*@ pred valid_counter(*mut u32 p; u32 v) =
    [_]is_u32(p) &*& *p |-> v;
@*/

/*@ pred valid_mutex(*mut Mutex m) =
    [_]is_Mutex(m) &*& *m |-> ?guard_val;
@*/

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
//@ ens valid_mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close valid_mutex(mutex);
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req valid_mutex(mutex);
//@ ens valid_mutex(mutex) &*& result == _;
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
//@ req CountPulsesData_pred(data, ?c, ?m, ?s) &*& valid_counter(c, ?v) &*& valid_mutex(m);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    //@ open CountPulsesData_pred(data, counter, mutex, source);

    loop {
        //@ inv valid_counter(counter, ?v0) &*& valid_mutex(mutex);
        wait_for_pulse(source);
        let guard = acquire(mutex);
        
        //@ open valid_counter(counter, v0);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close valid_counter(counter, v0 + 1);
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req valid_counter(counter, _) &*& valid_mutex(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_pred(data, counter, mutex, source);
    
    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        //@ close valid_counter(counter, 0);
        *counter = 0;
        
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            //@ inv valid_counter(counter, ?v) &*& valid_mutex(mutex);
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            
            //@ open valid_counter(counter, v);
            let count = *counter;
            //@ close valid_counter(counter, v);
            
            release(guard);
            print_u32(count);
        }
    }
}