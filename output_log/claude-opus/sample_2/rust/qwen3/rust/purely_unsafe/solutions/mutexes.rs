use std::alloc::{alloc, handle_alloc_error, Layout};

/*@

pred Mutex(mutex: *mut Mutex;) = (*mutex) |-> _;

pred MutexGuardToken(guard: MutexGuard, mutex: *mut Mutex;) = true;

pred Counter(counter: *mut u32; value: u32) = (*counter) |-> value;

pred CountPulsesData(data: CountPulsesData; counter: *mut u32, mutex: *mut Mutex, source: i32) =
    data.counter |-> counter &*&
    data.mutex |-> mutex &*&
    data.source |-> source;

pred CountPulsesInv(counter: *mut u32, mutex: *mut Mutex;) =
    [1/2]Mutex(mutex) &*& [1/2]Counter(counter, _);

@*/

struct Sendable<T> {
    payload: T,
}

unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req true;
//@ ens true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        unsafe { f(package_moved.payload) }
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
//@ req true;
//@ ens Mutex(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    //@ close Mutex(mutex);
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?f]Mutex(mutex);
//@ ens [f]Mutex(mutex) &*& MutexGuardToken(result, mutex);
{
    let guard = (*mutex).lock().unwrap();
    //@ close MutexGuardToken(guard, mutex);
    guard
}

unsafe fn release(guard: MutexGuard, mutex: *mut Mutex)
//@ req MutexGuardToken(guard, mutex);
//@ ens true;
{
    //@ open MutexGuardToken(guard, mutex);
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
//@ req CountPulsesData(data, ?counter, ?mutex, ?source) &*& [1/2]Mutex(mutex) &*& [1/2]Counter(counter, _);
//@ ens false;
{
    //@ open CountPulsesData(data, counter, mutex, source);
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop
    //@ inv [1/2]Mutex(mutex) &*& [1/2]Counter(counter, _);
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open [1/2]Counter(counter, _);

        let old_val = *counter;
        let new_val = old_val.checked_add(1).unwrap();
        *counter = new_val;

        //@ close [1/2]Counter(counter, new_val);
        release(guard, mutex);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [1/2]Mutex(mutex) &*& [1/2]Counter(counter, _);
//@ ens true;
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };
    //@ close CountPulsesData(data, counter, mutex, source);

    spawn(count_pulses, data);
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
        *counter = 0;
        //@ close Counter(counter, 0);

        let mutex = create_mutex();

        //@ close [1/2]Counter(counter, 0);
        //@ close [1/2]Counter(counter, 0);
        //@ close [1/2]Mutex(mutex);
        //@ close [1/2]Mutex(mutex);

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop
        //@ inv true;
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
        }
    }
}