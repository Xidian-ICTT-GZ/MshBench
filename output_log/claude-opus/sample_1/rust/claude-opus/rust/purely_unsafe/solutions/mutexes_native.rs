#![feature(mutex_data_ptr)]

use std::sync::Mutex;

predicate mutex_u32(m: *mut Mutex<u32>, v: u32) =
    // Owns the mutex at pointer m with inner value v
    m->Mutex<U32Mutex> &*&
    U32Mutex(m, v);

predicate U32Mutex(m: *mut Mutex<u32>, v: u32) =
    // Owns the inner data of the mutex: a u32 value v
    (*m).data_ptr() |-> v;

predicate counter_shared(counter: *mut Mutex<u32>) =
    // Half permission to the mutex, ensures value v exists
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

            // Obtain full ownership of the inner u32 value through the mutex guard
            // before incrementing it
            // Unlock returns the mutex_u32 predicate, so we require that
            // we hold the mutex_u32 predicate while locked
            //. This will match the half permission counter_shared predicate combined with
            // borrowing full ownership while locked.

            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

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

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop
        #[invariant(counter_shared(counter))]
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                let guard = (*counter).lock().unwrap();

                count = *(*counter).data_ptr();

                drop(guard);
            }

            print_u32(count);
        }
    }
}