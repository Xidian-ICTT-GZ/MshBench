//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error};

/*@ pred sendable<T>(Sendable<T>) = true; @*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ req true;
//@ ens true;
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    //@ close sendable(package);
    std::thread::spawn(move || {
        let package_moved = package;
        //@ open sendable(package_moved);
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

/*@ pred mutex_block(*mut Mutex) = alloc_block_::<Mutex>(_); @*/
/*@ pred mutex_full(*mut Mutex) = mutex_block(_) &*& (*_) |-> ?unit &*& unit == (); @*/

//@ req true;
//@ ens mutex_full(create_mutex());
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    //@ close mutex_block(mutex);
    mutex.write(Mutex::new(()));
    //@ close mutex_full(mutex);
    mutex
}

//@ req mutex_full(mutex);
//@ ens true;
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    //@ open mutex_full(mutex);
    let guard = (*mutex).lock().unwrap();
    //@ close mutex_block(mutex);
    guard
}

//@ req true;
//@ ens mutex_full(?mutex);
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
    //@ open mutex_block(?mutex);
    //@ assert (*mutex) |-> ?unit;
    //@ close mutex_full(mutex);
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

/*@ pred counter_block(*mut u32) = alloc_block_::<u32>(_); @*/
/*@ pred counter_full(*mut u32, u32) = counter_block(_) &*& (*_) |-> ?val &*& val == _1; @*/

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ req counter_full(counter, ?c) &*& mutex_full(mutex);
//@ ens true;
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ inv counter_full(counter, ?c) &*& mutex_full(mutex);
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_full(counter, c);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_full(counter, c + 1);
        release(guard);
    }
}

//@ req counter_full(counter, c) &*& mutex_full(mutex);
//@ ens true;
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        //@ close counter_block(counter);
        *counter = 0;
        //@ close counter_full(counter, 0);

        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            //@ inv counter_full(counter, ?c) &*& mutex_full(mutex);
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter_full(counter, c);
            let count = *counter;
            //@ close counter_full(counter, count);
            release(guard);
            print_u32(count);
        }
    }
}