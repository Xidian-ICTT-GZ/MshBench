#![feature(mutex_data_ptr)]

use std::sync::Mutex;

predicate mutex_own<T>(m: *mut Mutex<T>, v: T) = (*m).locked |-> false &*& struct_Mutex_padding::<T>(m) &*& *m |-> ?inner &*& inner == v;

predicate CountPulsesData_own(counter: *mut Mutex<u32>, source: i32) =
    mutex_own(counter, ?v) &*& v >= 0;

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

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

#[requires(CountPulsesData_own(counter, source))]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop
        invariant CountPulsesData_own(counter, source),
    {
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();
            open mutex_own(counter, _);
            let current = *(*counter).data_ptr();
            assert(current >= 0);
            let new_val = current + 1;
            *(*counter).data_ptr() = new_val;
            close mutex_own(counter, new_val);
            drop(guard);
        }
    }
}

#[requires(mutex_own(counter, ?v) &*& v >= 0)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };
    close CountPulsesData_own(counter, source);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        close mutex_own((&mutex) as *const _ as *mut _, 0);
        let counter = Box::into_raw(Box::new(mutex));

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop
            invariant mutex_own(counter, ?v) &*& v >= 0,
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                let guard = (*counter).lock().unwrap();
                open mutex_own(counter, _);
                count = *(*counter).data_ptr();
                assert(count >= 0);
                close mutex_own(counter, count);
                drop(guard);
            }

            print_u32(count);
        }
    }
}