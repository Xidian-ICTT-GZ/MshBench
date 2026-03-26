use std::alloc::{Layout, alloc, handle_alloc_error};

predicate_ctor is_Spawnee<T>(unsafe fn(T), predicate(T))();

predicate mutex_block(*mut Mutex) = [_]mutex_full(?m, ?t, ?d) &*& full_borrow(m, Mutex_full_borrow_content(t, d));

predicate counter_block(*mut u32, u32) = *?counter |-> ?v &*& counter == counter &*& v == v;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req is_Spawnee(f, ?pre)() &*& pre(arg);
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
//@ ens mutex_block(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_block(mutex);
//@ ens mutex_guard_full_borrow(?m, ?t, ?d, ?g) &*& full_borrow(m, Mutex_full_borrow_content(t, d)) &*& mutex_block(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_guard_full_borrow(?m, ?t, ?d, guard) &*& full_borrow(m, Mutex_full_borrow_content(t, d)) &*& mutex_block(?mutex);
//@ ens mutex_block(mutex);
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

predicate count_pulses_data_predicate(CountPulsesData) = 
    counter_block(?counter, ?v) &*& mutex_block(?mutex) &*& 
    result == CountPulsesData { counter: counter, mutex: mutex, source: _ };

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data_predicate(data);
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;

    loop 
    //@ inv counter_block(counter, ?v) &*& mutex_block(mutex) &*& source == source;
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        
        *counter = (*counter).checked_add(1).unwrap();
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter_block(counter, ?v) &*& mutex_block(mutex);
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    
    spawn(count_pulses, data);
    //@ close is_Spawnee(count_pulses, count_pulses_data_predicate)();
    //@ leak is_Spawnee(count_pulses, count_pulses_data_predicate)();
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter_block(counter, 0);
        
        let mutex = create_mutex();
        //@ assert mutex_block(mutex);

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop 
        //@ inv counter_block(counter, ?v) &*& mutex_block(mutex);
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            
            let count = *counter;
            
            release(guard);
            print_u32(count);
        }
    }
}