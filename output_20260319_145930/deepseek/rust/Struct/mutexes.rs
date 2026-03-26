use std::alloc::{Layout, alloc, handle_alloc_error};

/*@
pred mutex_own(?m: *mut Mutex) = 
    alloc_block(m, std::mem::size_of::<Mutex>()) &*& 
    struct_Mutex_padding(m);
@*/

/*@
pred mutex_guard_own(?g: MutexGuard, ?m: *mut Mutex) = true;
@*/

/*@
pred u32_ptr_own(?p: *mut u32) = 
    alloc_block(p, std::mem::size_of::<u32>()) &*& 
    u32__Ghost(p, _);
@*/

/*@
pred CountPulsesData_own(?data: CountPulsesData) = 
    data.counter |-> ?counter &*& 
    u32_ptr_own(counter) &*&
    data.mutex |-> ?mutex &*& 
    mutex_own(mutex) &*&
    data.source |-> ?source &*& 
    true;
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
//@ ens mutex_own(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_own(mutex);
//@ ens mutex_own(mutex) &*& mutex_guard_own(result, mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard_own(guard, ?mutex) &*& mutex_own(mutex);
//@ ens mutex_own(mutex);
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
//@ req CountPulsesData_own(data);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    //@ open CountPulsesData_own(_);
    loop {
        //@ invariant u32_ptr_own(counter) &*& mutex_own(mutex);
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open u32_ptr_own(counter);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close u32_ptr_own(counter);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req u32_ptr_own(counter) &*& mutex_own(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_own(data);
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
        //@ close u32_ptr_own(counter);
        
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            let count = *counter;
            release(guard);
            print_u32(count);
        }
    }
}