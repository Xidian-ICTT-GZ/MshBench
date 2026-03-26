use std::alloc::{Layout, alloc, handle_alloc_error};

/*@

pred u32_cell(p: *mut u32; v: u32) = std::alloc::alloc_block(p as *mut u8, Layout::new::<u32>()) &*& *(p) |-> v;

pred mutex_cell(p: *mut Mutex) = std::alloc::alloc_block(p as *mut u8, Layout::new::<Mutex>());

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
//@ ens mutex_cell(result);
unsafe fn create_mutex() -> *mut Mutex
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    //@ close mutex_cell(mutex);
    mutex
}

//@ req mutex_cell(mutex);
//@ ens mutex_cell(mutex);
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
{
    //@ open mutex_cell(mutex);
    let g = (*mutex).lock().unwrap();
    //@ close mutex_cell(mutex);
    g
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

//@ req true;
//@ ens true;
unsafe fn count_pulses(data: CountPulsesData)
{
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ inv true;
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

//@ req true;
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
        *counter = 0;

        let mutex = create_mutex();
        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            //@ inv true;
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}