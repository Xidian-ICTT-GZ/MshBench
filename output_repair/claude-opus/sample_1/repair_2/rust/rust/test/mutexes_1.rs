use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@
pred u32_at(p: *mut u32; v: u32) = *p |-> v;

pred mutex_at(p: *mut Mutex;) = (*p).0 |-> _;

pred counter_mutex_inv(counter: *mut u32, mutex: *mut Mutex;) =
    [1/2]u32_at(counter, _) &*& [1/2]mutex_at(mutex);

pred thread_token(counter: *mut u32, mutex: *mut Mutex;) =
    [1/4]u32_at(counter, _) &*& [1/4]mutex_at(mutex);
@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req true;
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

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens result != 0 as *mut Mutex &*& mutex_at(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]mutex_at(mutex);
//@ ens [f]mutex_at(mutex);
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
//@ req thread_token(data.counter, data.mutex);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    loop
    //@ inv thread_token(counter, mutex);
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open thread_token(counter, mutex);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close thread_token(counter, mutex);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req thread_token(counter, mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
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
        //@ close u32_at(counter, 0);

        let mutex = create_mutex();
        //@ close thread_token(counter, mutex);
        count_pulses_async(counter, mutex, 1);
        //@ close thread_token(counter, mutex);
        count_pulses_async(counter, mutex, 2);
        loop
        //@ inv [1/2]u32_at(counter, _) &*& [1/2]mutex_at(mutex);
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            let count = *counter;
            release(guard);
            print_u32(count);
        }
    }
}