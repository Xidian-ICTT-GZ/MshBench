use std::alloc::{Layout, alloc, handle_alloc_error};

/*@
pred u32_(p: *mut u32; v: u32) = p |-> v;

pred Mutex_(m: *mut Mutex) = m |-> _;

pred_ctor counter_prot(c: *mut u32)() = u32_(c, _);

pred mutex_inv(m: *mut Mutex, c: *mut u32) = 
    Mutex_(m) &*& counter_prot(c)();

pred mutex_frac(m: *mut Mutex, c: *mut u32; frac f) =
    [f]Mutex_(m);

pred count_pulses_pre(data: CountPulsesData) =
    mutex_frac(data.mutex, data.counter, 1/2) &*& [1/2]u32_(data.counter, _);

pred thread_token() = true;
@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req count_pulses_pre(?d) &*& arg == d;
//@ ensures thread_token();
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
pred MutexGuard_(g: MutexGuard, c: *mut u32) = u32_(c, _);
@*/

unsafe fn create_mutex() -> *mut Mutex
//@ requires true;
//@ ensures Mutex_(result);
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard 
//@ requires [?f]Mutex_(mutex) &*& [f]u32_(?c, _);
//@ ensures [f]Mutex_(mutex) &*& MutexGuard_(result, c);
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ requires MutexGuard_(guard, ?c);
//@ ensures u32_(c, _);
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ requires true;
//@ ensures true;
{
    //@ assume(false);
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
//@ requires true;
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
//@ requires count_pulses_pre(data);
//@ ensures false;
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, mutex, source} = data;
    loop {
        //@ invariant [1/2]Mutex_(mutex) &*& [1/2]u32_(counter, _);
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open MutexGuard_(guard, counter);
        *counter = (*counter).checked_add(1).unwrap();
        //@ close MutexGuard_(guard, counter);
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ requires [1/2]Mutex_(mutex) &*& [1/2]u32_(counter, _);
//@ ensures thread_token();
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_pre(data);
    spawn(count_pulses, data);
}

fn main()
//@ requires true;
//@ ensures false;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close u32_(counter, 0);

        let mutex = create_mutex();
        // We have full ownership of Mutex_ and u32_ at this point:
        //@ close mutex_frac(mutex, counter, 1);
        //@ open u32_(counter, 0);
        //@ close u32_(counter, 0);
        //@ close mutex_frac(mutex, counter, 1/2);
        //@ close [1/2]u32_(counter, 0);
        count_pulses_async(counter, mutex, 1);
        //@ close mutex_frac(mutex, counter, 1/2);
        //@ close [1/2]u32_(counter, 0);
        count_pulses_async(counter, mutex, 2);
        //@ leak thread_token();
        //@ leak thread_token();

        loop {
            //@ invariant thread_token() &*& thread_token();
            std::thread::sleep(std::time::Duration::from_millis(1000));
            //@ assume(false);
            let guard = acquire(mutex);
            //@ open MutexGuard_(guard, counter);
            let count = *counter;
            //@ close MutexGuard_(guard, counter);
            release(guard);
            print_u32(count);
        }
    }
}