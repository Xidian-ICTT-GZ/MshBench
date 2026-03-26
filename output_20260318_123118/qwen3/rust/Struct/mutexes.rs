use std::alloc::{Layout, alloc, handle_alloc_error};

predicate_ctor is_Spawnee<T>(unsafe fn(T), predicate(T))() = true;

predicate u32_ptr(*mut u32; u32) = *mut_u32_full(?p, ?v) &*& p == _ &*& v == _;

predicate mutex_ptr(*mut Mutex; ) = *mut_full(?p, ?m) &*& p == _ &*& Mutex_full(m);

predicate CountPulsesData_pred(CountPulsesData counter, mutex, source; ) =
    u32_ptr(counter, ?c) &*& mutex_ptr(mutex, );

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
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
//@ ens mutex_ptr(result, );
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_ptr(mutex, );
//@ ens mutex_ptr(mutex, ) &*& MutexGuard_full(result, ?t) &*& t == ();
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req MutexGuard_full(guard, ?t) &*& t == ();
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

lemma void CountPulsesData_split(CountPulsesData data; )
//@ requires CountPulsesData_pred(data, );
//@ ensures u32_ptr(data.counter, ?c) &*& mutex_ptr(data.mutex, ) &*& data.source |-> ?s;
{
    open CountPulsesData_pred(data, );
}

lemma void CountPulsesData_join(CountPulsesData data; )
//@ requires u32_ptr(data.counter, ?c) &*& mutex_ptr(data.mutex, ) &*& data.source |-> ?s;
//@ ensures CountPulsesData_pred(data, );
{
    close CountPulsesData_pred(data, );
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_pred(data, );
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    CountPulsesData_split(data);
    
    loop 
    //@ invariant u32_ptr(counter, ?c) &*& mutex_ptr(mutex, ) &*& source |-> ?s;
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        
        let old_val = *counter;
        *counter = old_val + 1;
        
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req u32_ptr(counter, ?c) &*& mutex_ptr(mutex, );
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    close CountPulsesData_pred(data, );
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
        close u32_ptr(counter, 0);
        
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop 
        //@ invariant u32_ptr(counter, ?c) &*& mutex_ptr(mutex, );
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            
            let count = *counter;
            
            release(guard);
            print_u32(count);
        }
    }
}