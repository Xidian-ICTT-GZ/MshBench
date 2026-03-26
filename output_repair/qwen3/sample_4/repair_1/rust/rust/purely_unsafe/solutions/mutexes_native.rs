#![feature(mutex_data_ptr)]

use std::sync::Mutex;
use std::ptr;

// Predicate representing ownership of a Mutex<u32> at a raw pointer
predicate mutex_u32(ptr: *mut Mutex<u32>) = {
    ptr != null() && 
    @*ptr as *const Mutex<u32> -> owned(Mutex<u32>, 1.0)
};

// Predicate for the data structure holding the counter and source
predicate count_pulses_data(data: CountPulsesData) = {
    mutex_u32(data.counter) &&
    data.source == _source_val // Placeholder for pure fact binding if needed, but struct fields are usually handled by value passing
};

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

unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

#[requires(mutex_u32(data.counter))]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop {
        #[invariant(mutex_u32(counter))]
        wait_for_pulse(source);

        {
            // Acquire lock requires full ownership of the Mutex
            let guard = (*counter).lock().unwrap();

            // Accessing data_ptr requires ownership of the inner u32 inside the Mutex
            // The predicate ensures we own the Mutex, which implies access to its contents while locked
            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

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

        let counter = Box::into_raw(Box::new(mutex));

        // Verify that we have ownership of the mutex before spawning threads
        #[assertion] mutex_u32(counter);

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
        
        // Cleanup: free the raw pointer (conceptually)
        // In VeriFast context, we assume the program runs until termination or explicit deallocation
        // Since this is an infinite loop in the example, we don't reach here naturally,
        // but the ownership predicate holds throughout.
    }
}