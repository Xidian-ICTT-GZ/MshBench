#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@

pred Mutex_share(m: *mut Mutex<u32>);

pred CountPulsesData_own(data: CountPulsesData; counter: *mut Mutex<u32>, source: i32) =
    data.counter |-> counter &*& data.source |-> source &*& Mutex_share(counter);

@*/

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

unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req CountPulsesData_own(data, ?counter, ?source);
//@ ens false;
{
    let CountPulsesData { counter, source } = data;
    //@ open CountPulsesData_own(data, counter, source);

    loop {
        //@ inv Mutex_share(counter);
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();

            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            drop(guard);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req Mutex_share(counter);
//@ ens true;
{
    let data = CountPulsesData { counter, source };
    //@ close CountPulsesData_own(data, counter, source);

    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ens false;
{
    unsafe {
        let mutex = Mutex::new(0);

        let counter = Box::into_raw(Box::new(mutex));
        //@ produce_lem_ptr_chunk Mutex_share(counter);

        //@ dup Mutex_share(counter);
        count_pulses_async(counter, 1);
        //@ dup Mutex_share(counter);
        count_pulses_async(counter, 2);

        loop {
            //@ inv Mutex_share(counter);
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