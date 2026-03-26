#![feature(mutex_data_ptr)]

use std::sync::Mutex;

predicate mutex_u32(m: *mut Mutex<u32>, v: u32) = 
    mutex_internal(m, v);

predicate mutex_internal(m: *mut Mutex<u32>, v: u32) = 
    // Abstract predicate for Mutex<u32> ownership with data v
    acc(m as ptr, 1) &*& *m == ?mutex &*&
    mutex.data_ptr() |-> ?p &*&
    p |-> v;

predicate counter_shared(counter: *mut Mutex<u32>) =
    [1/2]mutex_u32(counter, ?v);

predicate sendable<T>(s: Sendable<T>, payload: T) =
    s.payload |-> payload;

predicate count_pulses_data(d: CountPulsesData, counter: *mut Mutex<u32>, source: i32) =
    d.counter |-> counter &*& d.source |-> source &*& counter_shared(counter);

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[requires(true)]
#[ensures(true)]
unsafe fn spawn<T>(f: unsafe fn(arg: T), arg: T)
where
    T: 'static,
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
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
    counter: *mut Mutex<u32>,
    source: i32,
}

#[requires(count_pulses_data(data, ?counter, ?source))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop
    #[invariant(counter_shared(counter))]
    {
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();
            // The guard grants exclusive ownership of the Mutex data

            // Open the mutex_u32 predicate at full ownership heap chunk
            open counter_shared(counter);
            open mutex_u32(counter, ?v);

            let new_v = v.checked_add(1).unwrap();

            *(*counter).data_ptr() = new_v;

            close mutex_u32(counter, new_v);
            close counter_shared(counter);

            drop(guard);
        }
    }
}

#[requires(counter_shared(counter))]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };

    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);

        let counter = Box::into_raw(Box::new(mutex));

        // Initially full ownership of the mutex data
        close mutex_u32(counter, 0);

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop
        #[invariant(counter_shared(counter))]
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                let guard = (*counter).lock().unwrap();

                // Open the predicate at full ownership to access data
                open counter_shared(counter);
                open mutex_u32(counter, ?v);

                count = v;

                close mutex_u32(counter, v);
                close counter_shared(counter);

                drop(guard);
            }

            print_u32(count);
        }
    }
}