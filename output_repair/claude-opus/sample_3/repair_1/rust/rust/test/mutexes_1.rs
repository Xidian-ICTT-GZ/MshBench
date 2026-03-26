use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@
pred Mutex_own(p: *mut std::sync::Mutex<()>;) = malloc_block_Mutex(p);

pred_ctor counter_inv(counter: *mut u32, mutex: *mut std::sync::Mutex<()>)() =
    malloc_block_u32(counter) &*& u32_(counter, _);

pred thread_token(counter: *mut u32, mutex: *mut std::sync::Mutex<()>;) =
    [1/2]Mutex_own(mutex) &*& [_]mutex_inv(mutex, counter_inv(counter, mutex));

pred CountPulsesData_own(data: CountPulsesData;) =
    thread_token(data.counter, data.mutex);
@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req T_own(arg)
//@ ens true
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
//@ req true
//@ ens Mutex_own(result) &*& result != 0 as *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [_]mutex_inv(mutex, ?p) &*& [?f]Mutex_own(mutex)
//@ ens p() &*& [f]Mutex_own(mutex) &*& mutex_guard(result, mutex, p)
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard(guard, ?mutex, ?p) &*& p()
//@ ens true
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ req true
//@ ens true
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
//@ req true
//@ ens true
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req thread_token(data.counter, data.mutex)
//@ ens false
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ inv [1/2]Mutex_own(mutex) &*& [_]mutex_inv(mutex, counter_inv(counter, mutex))
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_inv(counter, mutex)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_inv(counter, mutex)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req thread_token(counter, mutex)
//@ ens true
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_own(data);
    spawn(count_pulses, data);
}

fn main()
//@ req true
//@ ens false
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;

        let mutex = create_mutex();
        //@ close counter_inv(counter, mutex)();
        //@ close mutex_inv(mutex, counter_inv(counter, mutex));
        //@ leak mutex_inv(mutex, counter_inv(counter, mutex));
        //@ close thread_token(counter, mutex);
        count_pulses_async(counter, mutex, 1);
        //@ close thread_token(counter, mutex);
        count_pulses_async(counter, mutex, 2);
        loop {
            //@ inv [_]mutex_inv(mutex, counter_inv(counter, mutex))
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter_inv(counter, mutex)();
            let count = *counter;
            //@ close counter_inv(counter, mutex)();
            release(guard);
            print_u32(count);
        }
    }
}