use std::alloc::{Layout, alloc, handle_alloc_error};

/*@ predicate mutex(Mutex* m;) = true; @*/
/*@ predicate counter(u32* c; int v) = c |-> v; @*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@
fixpoint predicate is_Spawnee<T>(unsafe fn(T) f, predicate(T) pre) { true }
@*/

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
//@ ensures mutex(result);
//@ terminates;
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req mutex(mutex);
//@ ensures mutex(mutex);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req true;
//@ ensures true;
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500)); 
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

/*@
predicate count_pulses_data(CountPulsesData data;) = 
  counter(data.counter, ?v) &*& mutex(data.mutex);
@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_data(data);
//@ ensures count_pulses_data(data);
//@ terminates(false);
{
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ open count_pulses_data(data);
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter(counter, ?old_count);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter(counter, old_count + 1);
        release(guard);
        //@ close count_pulses_data(data);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req counter(counter, ?v) &*& mutex(mutex);
//@ ensures true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_data(data);
    spawn(count_pulses, data);
}

fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter(counter, 0);

        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter(counter, ?count);
            let count = *counter;
            //@ close counter(counter, count);
            release(guard);
            print_u32(count);
        }
    }
}