use std::alloc::{Layout, alloc, handle_alloc_error};

/*@
predicate mutex_invariant() = true;
predicate mutex_handle(*mut Mutex) = 
    struct_Mutex_padding(_, _) &*& mutex_invariant();
predicate mutex_guard(MutexGuard) = true;
@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ req true;
//@ ens true;
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

//@ req true;
//@ ens mutex_handle(result);
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

//@ req mutex_handle(mutex);
//@ ens mutex_guard(result) &*& mutex_handle(mutex);
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    (*mutex).lock().unwrap()
}

//@ req mutex_guard(guard);
//@ ens true;
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
}

//@ req true;
//@ ens true;
unsafe fn wait_for_pulse(_source: i32)
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

//@ req true;
//@ ens true;
unsafe fn print_u32(n: u32)
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

/*@
predicate counter_handle(*mut u32; u32 value) = 
    alloc_block_u32(_, value);
predicate count_pulses_data(CountPulsesData data) = 
    counter_handle(data.counter, ?counter_val) &*& 
    mutex_handle(data.mutex) &*& 
    data.source |-> ?source_val;
@*/

//@ req count_pulses_data(data);
//@ ens false;
unsafe fn count_pulses(data: CountPulsesData)
{
    //@ open count_pulses_data(data);
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ inv counter_handle(counter, ?counter_val) &*& mutex_handle(mutex);
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_handle(mutex);
        //@ open counter_handle(counter, ?old_val);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_handle(counter, old_val + 1);
        //@ close mutex_handle(mutex);
        release(guard);
    }
}

//@ req counter_handle(counter, ?counter_val) &*& mutex_handle(mutex);
//@ ens true;
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data(data);
    spawn(count_pulses, data);
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter_handle(counter, 0);
        
        let mutex = create_mutex();
        
        //@ split_fraction mutex_handle(mutex)();
        //@ split_fraction mutex_handle(mutex)();
        //@ split_fraction counter_handle(counter, 0)();
        //@ split_fraction counter_handle(counter, 0)();
        
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        
        loop {
            //@ inv mutex_handle(mutex) &*& counter_handle(counter, ?count_val);
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_handle(mutex);
            //@ open counter_handle(counter, ?current_val);
            let count = *counter;
            //@ close counter_handle(counter, current_val);
            //@ close mutex_handle(mutex);
            release(guard);
            print_u32(count);
        }
    }
}