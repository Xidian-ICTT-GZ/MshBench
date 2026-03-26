use std::alloc::{alloc, handle_alloc_error, Layout};

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
pred mutex_inv(mutex: *mut Mutex, counter: *mut u32) =
    (*counter) |-> ?v;

pred mutex_held(mutex: *mut Mutex, counter: *mut u32) =
    (*counter) |-> ?v;

pred mutex_frac(mutex: *mut Mutex, counter: *mut u32; frac f) =
    [f](*mutex) |-> _;

pred count_pulses_data_inv(data: CountPulsesData) =
    data.counter |-> ?c &*& data.mutex |-> ?m &*& data.source |-> ?s &*&
    [1/2]mutex_frac(m, c; 1/2);
@*/

#[requires(true)]
#[ensures(true)]
unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T) {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

/*@
pred mutex_alloc(mutex: *mut Mutex) =
    (*mutex) |-> _;
@*/

#[ensures((*result) |-> _)]
unsafe fn create_mutex() -> *mut Mutex {
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() {
        handle_alloc_error(Layout::new::<Mutex>());
    }
    mutex.write(Mutex::new(()));
    mutex
}

#[requires((*mutex) |-> _)]
#[ensures((*mutex) |-> _)]
unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard {
    (*mutex).lock().unwrap()
}

#[requires(true)]
#[ensures(true)]
unsafe fn release(guard: MutexGuard) {
    drop(guard);
}

#[requires(true)]
#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

#[requires((*data.counter) |-> ?v &*& (*data.mutex) |-> _)]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData {
        counter,
        mutex,
        source,
    } = data;

    loop {
        //@ invariant (*counter) |-> ?cv &*& (*mutex) |-> _;
        wait_for_pulse(source);
        let guard = acquire(mutex);

        *counter = (*counter).checked_add(1).unwrap();

        release(guard);
    }
}

#[requires((*counter) |-> ?v &*& (*mutex) |-> _)]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32) {
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

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            //@ invariant true;
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);

            let count = *counter;

            release(guard);
            print_u32(count);
        }
    }
}