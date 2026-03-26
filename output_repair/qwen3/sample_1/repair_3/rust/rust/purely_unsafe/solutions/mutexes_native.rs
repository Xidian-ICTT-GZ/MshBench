#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

predicate mutex_own<T>(m: *mut Mutex<T>, v: T) = (*m).locked |-> false &*& (*m).data |-> v;

predicate CountPulsesData_own(counter: *mut Mutex<u32>, source: i32) =
    mutex_own(counter, ?count) &*& count >= 0;

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

#[requires(CountPulsesData_own(counter, source))]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop
        invariant CountPulsesData_own(counter, source);
    {
        wait_for_pulse(source);

        {
            open mutex_own(counter, ?count);
            assert (*counter).locked |-> false;
            (*counter).locked = true;
            assert (*counter).data |-> count;
            let new_count = count + 1;
            (*counter).data = new_count;
            (*counter).locked = false;
            close mutex_own(counter, new_count);
        }
    }
}

#[requires(mutex_own(counter, 0))]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };
    close CountPulsesData_own(counter, source);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        close mutex_own(&mutex as *const _ as *mut _, 0);
        let counter = Box::into_raw(Box::new(mutex));

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop
            invariant mutex_own(counter, ?c) &*& c >= 0;
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                open mutex_own(counter, ?c);
                assert (*counter).locked |-> false;
                (*counter).locked = true;
                assert (*counter).data |-> c;
                count = c;
                (*counter).locked = false;
                close mutex_own(counter, c);
            }

            print_u32(count);
        }
    }
}