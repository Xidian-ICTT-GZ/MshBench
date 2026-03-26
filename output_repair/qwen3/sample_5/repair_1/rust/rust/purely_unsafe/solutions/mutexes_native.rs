#![feature(mutex_data_ptr)]

use std::sync::Mutex;

predicate mutex_own<T>(m: *mut Mutex<T>, v: T) = (*m).lock() |-> v;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

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

#[requires(mutex_own(counter, ?v) &*& source == source_arg)]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop {
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();
            let current = *(*counter).data_ptr();
            assert(current < u32::MAX);
            *(*counter).data_ptr() = current + 1;
            drop(guard);
        }
    }
}

#[requires(mutex_own(counter, ?v))]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        let counter = Box::into_raw(Box::new(mutex));
        leak mutex_own(counter, 0);
        
        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
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