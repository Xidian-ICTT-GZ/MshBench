#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@
pred Mutex_u32(p: *mut Mutex<u32>; frac: real) =
    (*p).state |-> ?_ &*& frac > 0 &*& frac <= 1;

pred CountPulsesData_own(data: CountPulsesData; counter: *mut Mutex<u32>, source: i32) =
    data.counter |-> counter &*&
    data.source |-> source &*&
    [1/2]Mutex_u32(counter, 1/2);
@*/

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

#[requires(CountPulsesData_own(data, ?counter, ?source))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;
    /*@ open CountPulsesData_own(data, counter, source); @*/

    loop {
        /*@ invariant [1/2]Mutex_u32(counter, 1/2); @*/
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();

            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            drop(guard);
        }
    }
}

#[requires([1/2]Mutex_u32(counter, 1/2))]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };
    /*@ close CountPulsesData_own(data, counter, source); @*/

    spawn(count_pulses, data);
}

#[requires(true)]
#[ensures(false)]
fn main() {
    unsafe {
        let mutex = Mutex::new(0);

        let counter = Box::into_raw(Box::new(mutex));
        /*@ close [1/2]Mutex_u32(counter, 1/2); @*/
        /*@ close [1/2]Mutex_u32(counter, 1/2); @*/

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            /*@ invariant true; @*/
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