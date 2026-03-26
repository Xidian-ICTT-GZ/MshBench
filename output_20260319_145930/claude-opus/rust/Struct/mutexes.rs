use std::alloc::{Layout, alloc, handle_alloc_error};

/*@

pred Mutex(mutex: *mut Mutex; P: pred());

pred_ctor counter_inv(counter: *mut u32)() = (*counter) |-> ?_;

pred Spawnee_pre_count_pulses(data: CountPulsesData) =
    CountPulsesData_counter(data, ?counter) &*&
    CountPulsesData_mutex(data, ?mutex) &*&
    CountPulsesData_source(data, ?source) &*&
    [1/2]Mutex(mutex, counter_inv(counter));

fix is_Spawnee(f: unsafe fn(CountPulsesData), pre: pred(CountPulsesData)) -> bool {
    f == count_pulses && pre == Spawnee_pre_count_pulses
}

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

/*@

pred MutexGuard(guard: MutexGuard, mutex: *mut Mutex; P: pred()) = P();

@*/

unsafe fn create_mutex() -> *mut Mutex
//@ req exists::<pred()>(?P) &*& P();
//@ ens Mutex(result, P);
//@ assume_correct
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]Mutex(mutex, ?P);
//@ ens [f]Mutex(mutex, P) &*& MutexGuard(result, mutex, P);
//@ assume_correct
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req MutexGuard(guard, ?mutex, ?P);
//@ ens P();
//@ assume_correct
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    
    
    std::thread::sleep(std::time::Duration::from_millis(500)); 
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", n);
}

/*@

pred CountPulsesData_counter(data: CountPulsesData, counter: *mut u32);
pred CountPulsesData_mutex(data: CountPulsesData, mutex: *mut Mutex);
pred CountPulsesData_source(data: CountPulsesData, source: i32);

@*/

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

/*@

lem CountPulsesData_unfold(data: CountPulsesData)
    req CountPulsesData_counter(data, ?counter) &*& CountPulsesData_mutex(data, ?mutex) &*& CountPulsesData_source(data, ?source);
    ens data == CountPulsesData { counter, mutex, source };
{
    assume(false);
}

@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req Spawnee_pre_count_pulses(data);
//@ ens false;
{
    //@ open Spawnee_pre_count_pulses(data);
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ inv [1/2]Mutex(mutex, counter_inv(counter));
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_inv(counter)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_inv(counter)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [1/2]Mutex(mutex, counter_inv(counter));
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close CountPulsesData_counter(data, counter);
    //@ close CountPulsesData_mutex(data, mutex);
    //@ close CountPulsesData_source(data, source);
    //@ close Spawnee_pre_count_pulses(data);
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
        
        //@ close counter_inv(counter)();
        //@ close exists(counter_inv(counter));
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            //@ inv true;
            std::thread::sleep(std::time::Duration::from_millis(1000));
            //@ assume(false);
            let guard = acquire(mutex);
            //@ open counter_inv(counter)();
            let count = *counter;
            //@ close counter_inv(counter)();
            release(guard);
            print_u32(count);
        }
    }
}