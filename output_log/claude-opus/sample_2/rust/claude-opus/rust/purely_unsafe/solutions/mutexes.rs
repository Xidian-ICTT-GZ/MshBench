use std::alloc::{alloc, handle_alloc_error, Layout};
use std::sync::{Mutex as StdMutex, MutexGuard as StdMutexGuard};
use std::thread;
use std::time::Duration;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
predicate counter_inv(counter: *mut u32)() =
    counter |-> ?v;

predicate mutex_inv(mutex: *mut Mutex; p: pred()) =
    alloc_block(mutex as *mut u8, Layout::new_::<Mutex>()) &*&
    struct_Mutex_padding(mutex) &*&
    (*mutex).state |-> ?state &*&
    Mutex_state(mutex, state, p);

predicate thread_token(data: CountPulsesData) =
    data.counter |-> ?counter &*&
    data.mutex |-> ?mutex &*&
    data.source |-> ?source &*&
    [1/2]mutex_inv(mutex, counter_inv(counter));
@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req thread_token(?data) &*& data == arg;
//@ ensures true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = StdMutex<()>;
type MutexGuard = StdMutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ensures alloc_block(result as *mut u8, Layout::new_::<Mutex>()) &*& struct_Mutex_padding(result) &*& (*result).state |-> ?state &*& Mutex_state(result, state, counter_inv(?counter));
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(StdMutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]mutex_inv(mutex, ?p);
//@ ensures [f]mutex_inv(mutex, p) &*& p() &*& Mutex_guard_state(result, mutex);
{
    //@ open [f]mutex_inv(mutex, p);
    let result = (*mutex).lock().unwrap();
    //@ close [f]mutex_inv(mutex, p);
    result
}

unsafe fn release(guard: MutexGuard)
//@ req Mutex_guard_state(guard, ?mutex) &*& [?f]mutex_inv(mutex, ?p) &*& p();
//@ ensures [f]mutex_inv(mutex, p);
{
    //@ open [f]mutex_inv(mutex, p);
    drop(guard);
    //@ close [f]mutex_inv(mutex, p);
}

unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ensures true;
{
    std::thread::sleep(Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req thread_token(data);
//@ ensures false;
{
    //@ open thread_token(data);
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop
    //@ invariant [1/2]mutex_inv(mutex, counter_inv(counter));
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_inv(counter)();

        *counter = (*counter).checked_add(1).unwrap();

        //@ close counter_inv(counter)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [1/2]mutex_inv(mutex, counter_inv(counter));
//@ ensures true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    //@ close thread_token(data);
    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ensures false;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();
        //@ close counter_inv(counter)();
        //@ close mutex_inv(mutex, counter_inv(counter));

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop
        //@ invariant true;
        {
            std::thread::sleep(Duration::from_millis(1000));
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