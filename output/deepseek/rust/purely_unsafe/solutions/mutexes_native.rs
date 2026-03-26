#![feature(mutex_data_ptr)]
#![feature(ptr_metadata)]
#![feature(thread_local)]

use std::sync::Mutex;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

predicate mutex_own<T>(m: *mut Mutex<T>) -> bool {
    exists::<Box<Mutex<T>>>(|b| ptr::addr_of!(*b) == m)
}

predicate mutex_frac<T>(m: *mut Mutex<T>, f: rational) -> bool {
    exists::<Box<Mutex<T>>>(|b| ptr::addr_of!(*b) == m) && 0/1 < f && f <= 1/1
}

predicate mutex_locked<T>(m: *mut Mutex<T>, f: rational, v: T) -> bool {
    exists::<Box<Mutex<T>>>(|b| ptr::addr_of!(*b) == m) && 0/1 < f && f <= 1/1
}

#[requires(mutex_own(counter))]
#[ensures(mutex_own(counter))]
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

predicate count_pulses_data_own(data: CountPulsesData) -> bool {
    exists::<rational>(|f| mutex_frac(data.counter, f))
}

#[requires(count_pulses_data_own(data))]
#[ensures(count_pulses_data_own(data))]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    #[invariant(count_pulses_data_own(CountPulsesData { counter, source }))]
    loop {
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();

            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            drop(guard);
        }
    }
}

#[requires(mutex_own(counter))]
#[ensures(mutex_own(counter))]
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

        #[invariant(mutex_own(counter))]
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