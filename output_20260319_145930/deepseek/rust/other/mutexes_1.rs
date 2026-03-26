use std::alloc::{Layout, alloc, handle_alloc_error};

/*@
pred alloc_block_u32(p: *mut u32) = 
    struct_u32_ptr(p, _) &*& malloc_block_u32(p);
pred struct_u32_ptr(p: *mut u32, v: u32) = 
    *p |-> v;
pred malloc_block_u32(p: *mut u32) = true;

pred mutex_ptr(p: *mut Mutex) = 
    struct_mutex_ptr(p, _) &*& malloc_block_mutex(p);
pred struct_mutex_ptr(p: *mut Mutex, v: Mutex) = 
    *p |-> v;
pred malloc_block_mutex(p: *mut Mutex) = true;

pred mutex_guard(g: MutexGuard) = true;
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
//@ ens mutex_ptr(result);
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close malloc_block_mutex(mutex);
    //@ close struct_mutex_ptr(mutex, _);
    //@ close mutex_ptr(mutex);
    mutex.write(Mutex::new(()));
    mutex
}

//@ req mutex_ptr(mutex);
//@ ens mutex_ptr(mutex) &*& mutex_guard(result);
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    //@ open mutex_ptr(mutex);
    //@ open struct_mutex_ptr(mutex, _);
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
pred count_pulses_data(data: CountPulsesData) = 
    alloc_block_u32(data.counter) &*& mutex_ptr(data.mutex) &*& data.source |-> _;
@*/

//@ req count_pulses_data(data);
//@ ens false;
unsafe fn count_pulses(data: CountPulsesData)
{
    //@ open count_pulses_data(data);
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ inv alloc_block_u32(counter) &*& mutex_ptr(mutex) &*& source |-> _;
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_ptr(mutex);
        //@ open alloc_block_u32(counter);
        //@ open struct_u32_ptr(counter, _);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close struct_u32_ptr(counter, _);
        //@ close alloc_block_u32(counter);
        //@ close mutex_ptr(mutex);
        release(guard);
    }
}

//@ req alloc_block_u32(counter) &*& mutex_ptr(mutex) &*& source |-> _;
//@ ens true;
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    //@ close count_pulses_data(CountPulsesData { counter, mutex, source });
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        //@ close malloc_block_u32(counter);
        //@ close struct_u32_ptr(counter, 0);
        //@ close alloc_block_u32(counter);
        *counter = 0;
        
        let mutex = create_mutex();
        //@ open alloc_block_u32(counter);
        count_pulses_async(counter, mutex, 1);
        //@ close alloc_block_u32(counter);
        //@ open alloc_block_u32(counter);
        count_pulses_async(counter, mutex, 2);
        //@ close alloc_block_u32(counter);
        
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_ptr(mutex);
            //@ open alloc_block_u32(counter);
            //@ open struct_u32_ptr(counter, _);
            let count = *counter;
            //@ close struct_u32_ptr(counter, _);
            //@ close alloc_block_u32(counter);
            //@ close mutex_ptr(mutex);
            release(guard);
            print_u32(count);
        }
    }
}