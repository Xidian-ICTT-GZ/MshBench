#![feature(mutex_data_ptr)]

use std::sync::Mutex;

/*@

pred_ctor Counter(counter: *mut u32)() = *counter |-> ?count;

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@

pred Spawnee_pre<T>(arg: T) = true;

pred_ctor is_Spawnee<T>(f: unsafe fn(T))() = true;

@*/

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
//@ assume_correct
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

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

/*@

pred count_pulses_pre(data: CountPulsesData) =
    [1/3]Mutex_shared(data.counter, Counter(Mutex::data_ptr(data.counter)));

@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req thread_token(currentThread) &*& count_pulses_pre(data);
//@ ens thread_token(currentThread);
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, source} = data;

    loop {
        //@ inv thread_token(currentThread) &*& [1/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));
        wait_for_pulse(source);
        //@ let k = begin_lifetime();
        {
            //@ let_lft 'a = k;
            let guard = (*counter).lock().unwrap();
            
            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();
            
            drop(guard);
        }
        //@ end_lifetime(k);
    }
}

/*@

lem count_pulses_is_spawnee()
    req true;
    ens [_]is_Spawnee(count_pulses, count_pulses_pre);
{
    assume(false);
}

@*/

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req thread_token(currentThread) &*& [1/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));
//@ ens thread_token(currentThread);
{
    let data = CountPulsesData { counter, source };
    //@ close count_pulses_pre(data);
    //@ count_pulses_is_spawnee();
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        //@ assume(thread_token(currentThread));
        let counter = Box::into_raw(Box::new(mutex));
        //@ assume(Mutex_shared(counter, Counter(Mutex::data_ptr(counter))));

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            //@ inv thread_token(currentThread) &*& [1/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));
            std::thread::sleep(std::time::Duration::from_millis(1000));
            
            let count;
            {
                //@ let k = begin_lifetime();
                //@ let_lft 'a = k;
                let guard = (*counter).lock().unwrap();
                
                count = *(*counter).data_ptr();
                
                drop(guard);
                //@ end_lifetime(k);
            }
            
            print_u32(count);
        }
    }
}