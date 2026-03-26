//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error};

/*@ pred Sendable_own<T>(Sendable<T>) = true; @*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@ pred is_Spawnee<T>(unsafe fn(T), pred<T>) = true; @*/

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

/*@ pred mutex_own(*mut Mutex) = true; @*/
/*@ pred u32_own(*mut u32, u32) = true; @*/

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex);
//@ ens mutex_own(mutex);
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

/*@ pred CountPulsesData_own(CountPulsesData, *mut u32, *mut Mutex, i32) = true; @*/

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data, ?counter, ?mutex, ?source) &*& u32_own(counter, _) &*& mutex_own(mutex);
//@ ens true;
{
    let CountPulsesData {counter, mutex, source} = data;
    //@ open CountPulsesData_own(_, _, _, _);
    loop {
        //@ inv u32_own(counter, _) &*& mutex_own(mutex);
        wait_for_pulse(source);
        let guard = acquire(mutex);
        *counter = (*counter).checked_add(1).unwrap();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req u32_own(counter, _) &*& mutex_own(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_own(data, counter, mutex, source);
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
        //@ close u32_own(counter, 0);
        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            //@ inv u32_own(counter, _) &*& mutex_own(mutex);
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            let count = *counter;
            release(guard);
            print_u32(count);
        }
    }
}