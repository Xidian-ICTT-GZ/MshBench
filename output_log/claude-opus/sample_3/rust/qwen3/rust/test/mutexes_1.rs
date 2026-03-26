use std::alloc::{Layout, alloc, handle_alloc_error};
use std::sync::{Mutex as StdMutex, MutexGuard as StdMutexGuard};
use std::thread;

#[pred]
pred mutex_inv(mutex: *mut Mutex, g: option<MutexGuard>) = 
    mutex |-> ?m &*& m == StdMutex::new(()) &*&
    switch (g) {
        case None => true;
        case Some(guard) => guard |-> MutexGuard(())
    };

#[pred]
pred Mutex(mutex_val: StdMutex<()>) = true; 

#[pred]
pred MutexGuard(guard_val: ()) = true;

#[pred]
pred counter_inv(counter: *mut u32, v: u32) =
    counter |-> v;

#[pred]
pred count_pulses_data_inv(data: CountPulsesData) =
    counter_inv(data.counter, ?cv) &*&
    mutex_inv(data.mutex, None) &*&
    data.source |-> ?s;

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
#[requires(count_pulses_data_inv(arg))]
#[ensures(true)]
{
    let package = Sendable { payload: arg };
    thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = StdMutex<()>;
type MutexGuard = StdMutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
#[requires(true)]
#[ensures(result |-> StdMutex::new(()))]
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(StdMutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
#[requires(mutex |-> ?m &*& m == StdMutex::new(()))]
#[ensures(result |-> MutexGuard(()) &*& mutex |-> m)]
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
#[requires(guard |-> MutexGuard(()))]
#[ensures(true)]
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
#[requires(true)]
#[ensures(true)]
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
#[requires(true)]
#[ensures(true)]
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
#[requires(
    counter_inv(data.counter, ?c) &*&
    mutex_inv(data.mutex, None) &*&
    data.source |-> ?s
)]
#[ensures(false)]
{
    let CountPulsesData { counter, mutex, source } = data;
    loop {
        wait_for_pulse(source);
        let guard = acquire(mutex);
        #[invariant(
            counter_inv(counter, ?c) &*&
            mutex_inv(mutex, Some(guard)) &*&
            guard |-> MutexGuard(())
        )]
        {
            *counter = c + 1;
        }
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
#[requires(
    counter_inv(counter, ?c) &*&
    mutex_inv(mutex, None) &*&
    true
)]
#[ensures(true)]
{
    let data = CountPulsesData { counter, mutex, source };
    spawn(count_pulses, data);
}

fn main()
#[requires(true)]
#[ensures(true)]
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        #[assert(counter |-> 0);]

        let mutex = create_mutex();
        #[assert(mutex |-> StdMutex::new(()));]

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);
        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            #[invariant(
                counter_inv(counter, ?c) &*&
                mutex_inv(mutex, Some(guard)) &*&
                guard |-> MutexGuard(())
            )]
            {
                let count = *counter;
                release(guard);
                print_u32(count);
            }
        }
    }
}