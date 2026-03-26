use std::alloc::{Layout, alloc, handle_alloc_error};
/*@ 
  pred alloc_block_Mutex(mutex: *mut Mutex) = mutex != 0 &*& chars(mutex as usize, sizeof<Mutex>, _);
  pred alloc_block_u32(p: *mut u32) = p != 0 &*& chars(p as usize, sizeof<u32>, _);
  pred mutex_data(mutex: *mut Mutex) = alloc_block_Mutex(mutex);
  pred counter_data(counter: *mut u32, v: u32) = alloc_block_u32(counter) &*& *counter |-> v;
@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ req true;
//@ ens true;
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}
type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

//@ req true;
//@ ens mutex_data(result);
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

//@ req mutex_data(mutex);
//@ ens true; // conservatively
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    (*mutex).lock().unwrap()
}

//@ req true;
//@ ens true;
unsafe fn release(guard: MutexGuard)
{
    drop(guard);
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

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ req mutex_data(data.mutex) &*& counter_data(data.counter, _);
//@ ens true;
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_data(counter, _);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_data(counter, *counter);
        release(guard);
    }
}

//@ req mutex_data(mutex) &*& counter_data(counter, _);
//@ ens true;
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter_data(counter, 0);

        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter_data(counter, _);
            let count = *counter;
            //@ close counter_data(counter, count);
            release(guard);
            print_u32(count);
        }
    }
}