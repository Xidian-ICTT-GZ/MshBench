#![feature(mutex_data_ptr)]

use std::sync::Mutex;

/*@

pred mutex_u32(m: *mut Mutex<u32>, v: u32) = 
    (*m).Mutex(v);

pred counter_shared(counter: *mut Mutex<u32>) =
    [1/2](*counter).Mutex(_);

pred count_pulses_data(d: CountPulsesData, counter: *mut Mutex<u32>, source: i32) =
    d.counter |-> counter &*& d.source |-> source &*& counter_shared(counter);

@*/

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
    //@ open count_pulses_data(data, counter, source);
    let CountPulsesData { counter, source } = data;

    loop
    //@ inv counter_shared(counter)
    {
        wait_for_pulse(source);

        {
            //@ open counter_shared(counter);
            let guard = (*counter).lock().unwrap();

            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            drop(guard);
            //@ close counter_shared(counter);
        }
    }
}

#[requires(count_pulses_data(?data, counter, source))]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };
    //@ close count_pulses_data(data, counter, source);

    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);

        let counter = Box::into_raw(Box::new(mutex));
        //@ close [1/2](*counter).Mutex(_);
        //@ close counter_shared(counter);
        //@ close [1/2](*counter).Mutex(_);
        //@ close counter_shared(counter);

        //@ close count_pulses_data(CountPulsesData { counter, source: 1 }, counter, 1);
        count_pulses_async(counter, 1);
        //@ close count_pulses_data(CountPulsesData { counter, source: 2 }, counter, 2);
        count_pulses_async(counter, 2);

        loop
        //@ inv counter_shared(counter)
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                //@ open counter_shared(counter);
                let guard = (*counter).lock().unwrap();

                count = *(*counter).data_ptr();

                drop(guard);
                //@ close counter_shared(counter);
            }

            print_u32(count);
        }
    }
}