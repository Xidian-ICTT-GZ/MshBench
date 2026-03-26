#![feature(mutex_data_ptr)]

use std::sync::Mutex;

//@ predicate Counter(counter: *mut u32, count: u32) = *counter |-> count;

//@ predicate mutex_counter(mutex: *mut Mutex<u32>, count: u32) =
//@     Mutex(mutex, mutex_inv(mutex, count)) &*& mutex_inv(mutex, count);
//@ predicate mutex_inv(mutex: *mut Mutex<u32>, count: u32) =
//@     exists(counter: *mut u32) &*& mutex.data_ptr() == counter &*& Counter(counter, count);

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T>(f: unsafe fn(arg: T), arg: T)
    where T: 'static
//@ requires [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ensures true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

unsafe fn wait_for_pulse(_source: i32)
//@ requires true;
//@ ensures true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
//@ requires true;
//@ ensures true;
{
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

//@ predicate count_pulses_pre(data: CountPulsesData, count: u32) =
//@     mutex_counter(data.counter, count);

unsafe fn count_pulses(data: CountPulsesData)
//@ requires thread_token(currentThread) &*& count_pulses_pre(data, ?count);
//@ ensures thread_token(currentThread) &*& count_pulses_pre(data, count + 1);
{
    //@ open count_pulses_pre(data, count);
    let CountPulsesData {counter, source} = data;

    loop {
        //@ invariant thread_token(currentThread) &*& count_pulses_pre(data, count);
        wait_for_pulse(source);

        {
            //@ open mutex_counter(counter, count);
            let guard = (*counter).lock().unwrap();
            let counter_ptr: *mut u32 = (*counter).data_ptr();

            //@ open Counter(counter_ptr, count);
            *counter_ptr = count + 1;
            //@ close Counter(counter_ptr, count + 1);
            count = count + 1;

            drop(guard);
            //@ close mutex_counter(counter, count);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ requires mutex_counter(counter, ?count);
//@ ensures true;
{
    let data = CountPulsesData { counter, source };

    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        let counter = Box::into_raw(Box::new(mutex));

        //@ close Counter((*counter).data_ptr(), 0);
        //@ close mutex_counter(counter, 0);

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                //@ open mutex_counter(counter, ?c);
                let guard = (*counter).lock().unwrap();
                count = *(*counter).data_ptr();
                drop(guard);
                //@ close mutex_counter(counter, c);
            }
            print_u32(count);
        }
    }
}