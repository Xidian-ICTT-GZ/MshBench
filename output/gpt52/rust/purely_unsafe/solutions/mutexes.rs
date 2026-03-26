use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@

predicate malloc_block_Mutex(*mut Mutex p);
predicate malloc_block_u32(*mut u32 p);

predicate mutex_box(*mut Mutex p) =
    malloc_block_Mutex(p);

predicate counter_box(*mut u32 p; u32 v) =
    malloc_block_u32(p) &*& *p |-> v;

predicate shared_counter(*mut u32 counter, *mut Mutex mutex) =
    mutex_box(mutex) &*& exists<u32>(?v) &*& counter_box(counter, v);

predicate CountPulsesData_pred(struct CountPulsesData data) =
    shared_counter(data.counter, data.mutex);

@*/

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
/*@ requires is_sendable<T>() &*& (forall(T t) (requires true; ensures true)) == f &*& true; @*/
/*@ ensures true; @*/
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
/*@ requires true; @*/
/*@ ensures mutex_box(result); @*/
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
/*@ requires mutex_box(mutex); @*/
/*@ ensures mutex_box(mutex); @*/
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
/*@ requires true; @*/
/*@ ensures true; @*/
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
/*@ requires true; @*/
/*@ ensures true; @*/
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
/*@ requires true; @*/
/*@ ensures true; @*/
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
/*@ requires CountPulsesData_pred(data); @*/
/*@ ensures false; @*/
{
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop
    /*@ invariant shared_counter(counter, mutex); @*/
    {
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
/*@ requires shared_counter(counter, mutex); @*/
/*@ ensures true; @*/
{
    let data = CountPulsesData {
        counter,
        mutex,
        source,
    };

    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;

        let mutex = create_mutex();

        /*@ close counter_box(counter, 0); @*/
        /*@ close shared_counter(counter, mutex); @*/
        count_pulses_async(counter, mutex, 1);
        /*@ close shared_counter(counter, mutex); @*/
        count_pulses_async(counter, mutex, 2);

        loop
        /*@ invariant shared_counter(counter, mutex); @*/
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}