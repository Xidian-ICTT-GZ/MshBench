use std::alloc::{Layout, alloc, handle_alloc_error};

/*@
predicate_ctor mutex_ctor(place: *mut Mutex)() = 
    struct_Mutex_padding(place) &*& (*place).data |-> ?inner &*& inner == Mutex_data(0, false);
predicate mutex_invariant(place: *mut Mutex) = [_]mutex_ctor(place)();
predicate mutex(place: *mut Mutex) = 
    alloc_block(place, std::mem::size_of::<Mutex>()) &*& mutex_invariant(place);
predicate mutex_held(place: *mut Mutex, guard: MutexGuard) = 
    guard == MutexGuard(place) &*& mutex_invariant(place);
@*/

/*@
predicate_ctor spawnee_pre_count_pulses(CountPulsesData data)() = 
    mutex(data.mutex) &*& 
    alloc_block(data.counter, std::mem::size_of::<u32>()) &*& 
    *data.counter |-> ?val;
predicate is_Spawnee(unsafe fn(CountPulsesData) f, predicate(CountPulsesData) pre) = 
    f == count_pulses &*& pre == spawnee_pre_count_pulses;
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
//@ ens mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_ctor(mutex)();
    //@ close mutex_invariant(mutex);
    //@ close mutex(mutex);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex(mutex);
//@ ens mutex_held(mutex, result);
{
    //@ open mutex(mutex);
    //@ open mutex_invariant(mutex);
    //@ open mutex_ctor(mutex)();
    let guard = (*mutex).lock().unwrap();
    //@ close mutex_held(mutex, guard);
    guard
}

unsafe fn release(guard: MutexGuard)
//@ req mutex_held(?mutex, guard);
//@ ens mutex(mutex);
{
    //@ open mutex_held(?mutex, guard);
    drop(guard);
    //@ close mutex_invariant(mutex);
    //@ close mutex(mutex);
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

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req spawnee_pre_count_pulses(data)();
//@ ens false;
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ invariant mutex(mutex) &*& alloc_block(counter, std::mem::size_of::<u32>()) &*& *counter |-> ?val;
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open mutex_held(mutex, guard);
        //@ open mutex_invariant(mutex);
        //@ open mutex_ctor(mutex)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close mutex_ctor(mutex)();
        //@ close mutex_invariant(mutex);
        //@ close mutex_held(mutex, guard);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req mutex(mutex) &*& alloc_block(counter, std::mem::size_of::<u32>()) &*& *counter |-> ?val;
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close spawnee_pre_count_pulses(data)();
    //@ close is_Spawnee(count_pulses, spawnee_pre_count_pulses)();
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
        
        let mutex = create_mutex();

        //@ close mutex(mutex);
        //@ close mutex(mutex);
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open mutex_held(mutex, guard);
            //@ open mutex_invariant(mutex);
            //@ open mutex_ctor(mutex)();
            let count = *counter;
            //@ close mutex_ctor(mutex)();
            //@ close mutex_invariant(mutex);
            //@ close mutex_held(mutex, guard);
            release(guard);
            print_u32(count);
        }
    }
}