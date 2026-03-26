#![feature(mutex_data_ptr)]

use std::sync::Mutex;
use std::ptr;

predicate mutex_u32(ptr: *mut Mutex<u32>) = (*ptr) |-> ?m &*& [_]mutex(m, ?inner) &*& inner |-> ?v &*& v == _;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[requires(true)]
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
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

#[requires(mutex_u32(counter))]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop {
        #[invariant(mutex_u32(counter))]
        {
            wait_for_pulse(source);

            let guard = (*counter).lock().unwrap();
            let current = *(*counter).data_ptr();
            let next = current.checked_add(1).unwrap();
            *(*counter).data_ptr() = next;
            drop(guard);
        }
    }
}

#[requires(mutex_u32(counter))]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        let boxed = Box::new(mutex);
        let counter = Box::into_raw(boxed);

        // Transfer ownership to predicate
        assert mutex_u32(counter);

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let guard = (*counter).lock().unwrap();
            let count = *(*counter).data_ptr();
            drop(guard);

            print_u32(count);
        }
    }
}