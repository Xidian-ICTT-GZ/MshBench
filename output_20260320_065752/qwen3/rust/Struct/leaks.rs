#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

/*@ pred is_Spawnee<T>(unsafe fn(T), predicate(T)) = true; @*/

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

/*@ pred mutex_block(*mut Mutex, _) = true; @*/
/*@ pred counter_block(*mut u32, _) = true; @*/

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens mutex_block(result, ());
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close mutex_block(mutex, ());
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_block(mutex, ?v);
//@ ens mutex_block(mutex, v);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
//@ ens true;
{
    drop(guard);
}

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
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

/*@ pred count_pulses_data(CountPulsesData, *mut u32, *mut Mutex, i32) =
    counter == counter && mutex == mutex && source == source &*&
    counter_block(counter, ?c) &*& mutex_block(mutex, ?m); @*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data(data, ?counter, ?mutex, ?source) &*& counter_block(counter, ?c) &*& mutex_block(mutex, ?m);
//@ ens true;
{
    
    let CountPulsesData {counter, mutex, source} = data;
    //@ open count_pulses_data(_ , _, _, _);

    loop {
        //@ inv counter_block(counter, ?c) &*& mutex_block(mutex, ?m);
        
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open mutex_block(mutex, m);
        
        *counter = (*counter).checked_add(1).unwrap();
        //@ close mutex_block(mutex, c + 1);
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_block(counter, ?c) &*& mutex_block(mutex, ?m);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data(data, counter, mutex, source);
    
    
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

/*@ pred print_count_data(PrintCountData, *mut u32, *mut Mutex) =
    counter == counter && mutex == mutex &*&
    counter_block(counter, ?c) &*& mutex_block(mutex, ?m); @*/

unsafe fn print_count(data: PrintCountData)
//@ req print_count_data(data, ?counter, ?mutex) &*& counter_block(counter, ?c) &*& mutex_block(mutex, ?m);
//@ ens true;
{
    
    let PrintCountData {counter, mutex} = data;
    //@ open print_count_data(_, _, _);
    loop {
        //@ inv counter_block(counter, ?c) &*& mutex_block(mutex, ?m);
        
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open mutex_block(mutex, ?m_val);
        
        print_u32(*counter);
        //@ close mutex_block(mutex, m_val);
        
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req counter_block(counter, ?c) &*& mutex_block(mutex, ?m);
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close print_count_data(data, counter, mutex);
    
    
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        //@ close counter_block(counter, 0);
        *counter = 0;
        
        
        let mutex = create_mutex();
        

        print_count_async(counter, mutex);

        loop {
            
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}