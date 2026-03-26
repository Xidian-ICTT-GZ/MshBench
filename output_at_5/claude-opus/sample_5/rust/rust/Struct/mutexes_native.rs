#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T>(f: unsafe fn(arg: T), arg: T)
    where T: 'static
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
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
//@ assume_correct
{
    println!("{}", n);
}

//@ pred_ctor Counter(counter: *mut u32)() = *counter |-> ?count;

/*@

predicate mutex_counter_shared(m: *mut Mutex<u32>, counter: *mut u32) = 
    // abstract predicate representing ownership of the mutex m 
    // and the predicate Counter attached to the mutex's data_ptr()
    [&1/3]m->Mutex::data_ptr() &*& Counter(counter);

pred count_pulses_pre(data: CountPulsesData) =
    mutex_counter_shared(data.counter, Mutex::data_ptr(data.counter));

@*/

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req thread_token(currentThread) &*& count_pulses_pre(data);
//@ ens thread_token(currentThread);
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, source} = data;

    loop {
        //@ inv thread_token(currentThread) &*& mutex_counter_shared(counter, Mutex::data_ptr(counter));
        wait_for_pulse(source);
        //@ let k = begin_lifetime();
        {
            //@ let_lft 'a = k;
            let guard = (*counter).lock().unwrap();
            //@ open Counter((*counter).data_ptr())();

            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            //@ close Counter((*counter).data_ptr())();
            drop(guard);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req thread_token(currentThread) &*& count_pulses_pre(CountPulsesData { counter, source });
//@ ens thread_token(currentThread);
{
    let data = CountPulsesData { counter, source };
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        //@ close Counter(mutex.data_ptr())();
        //@ close mutex_counter_shared(&mutex, mutex.data_ptr());

        let counter = Box::into_raw(Box::new(mutex));
        //@ close count_pulses_pre(CountPulsesData { counter, source: 0 });

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                let guard = (*counter).lock().unwrap();
                //@ open Counter((*counter).data_ptr())();
                count = *(*counter).data_ptr();
                //@ close Counter((*counter).data_ptr())();
                drop(guard);
            }

            print_u32(count);
        }
    }
}