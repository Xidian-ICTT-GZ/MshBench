use std::alloc::{Layout, alloc, handle_alloc_error};

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

predicate malloc_block_u32(*mut u32 p);
predicate malloc_block_Mutex(*mut Mutex p);

predicate counter_ptr(*mut u32 p; u32 v) = malloc_block_u32(p) &*& *p |-> v;

predicate mutex_ptr(*mut Mutex p) = malloc_block_Mutex(p);

predicate shared_state(*mut u32 counter, *mut Mutex mutex; u32 v) =
    counter_ptr(counter, v) &*& mutex_ptr(mutex);

predicate inv_state(*mut u32 counter, *mut Mutex mutex) =
    exists<u32>(?v) &*& shared_state(counter, mutex, v);

predicate pulse_thread_data(CountPulsesData data) =
    inv_state(data.counter, data.mutex);

@*/

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens result != 0 &*& mutex_ptr(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex_ptr(mutex);
//@ ens mutex_ptr(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
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

unsafe fn count_pulses(data: CountPulsesData)
//@ req pulse_thread_data(data);
//@ ens true;
{
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ invariant inv_state(counter, mutex);
        wait_for_pulse(source);
        let guard = acquire(mutex);

        //@ open inv_state(counter, mutex);
        //@ open exists(?v);
        //@ open shared_state(counter, mutex, v);
        //@ open counter_ptr(counter, v);
        //@ open mutex_ptr(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        //@ close counter_ptr(counter, v + 1);
        //@ close mutex_ptr(mutex);
        //@ close shared_state(counter, mutex, v + 1);
        //@ close inv_state(counter, mutex);

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req inv_state(counter, mutex);
//@ ens inv_state(counter, mutex);
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close pulse_thread_data(data);
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

        //@ assume(counter != 0);
        //@ close malloc_block_u32(counter);
        //@ close counter_ptr(counter, 0);

        let mutex = create_mutex();

        //@ close shared_state(counter, mutex, 0);
        //@ close inv_state(counter, mutex);

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            //@ invariant inv_state(counter, mutex);
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            //@ open inv_state(counter, mutex);
            //@ open exists(?v);
            //@ open shared_state(counter, mutex, v);
            //@ open counter_ptr(counter, v);
            //@ open mutex_ptr(mutex);

            let count = *counter;

            //@ close counter_ptr(counter, v);
            //@ close mutex_ptr(mutex);
            //@ close shared_state(counter, mutex, v);
            //@ close inv_state(counter, mutex);

            release(guard);
            print_u32(count);
        }
    }
}