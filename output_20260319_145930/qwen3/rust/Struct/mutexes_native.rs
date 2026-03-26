#![feature(mutex_data_ptr)]

use std::sync::Mutex;

/*@ pred_ctor Counter(counter: *mut u32)() = *counter |-> ?count; @*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@ pred is_Spawnee<T>(f: unsafe fn(arg: T), pre: predicate(T)) =
    forall t, pre(t) ==>
        call_requires(f)(t) &*&
        call_ensures(f)(t, unit);
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
            //@ open Mutex_locked(?k_counter, ?k_inv, ?frac, _);
            //@ open Counter(k_counter)();
            let old_count = *(*counter).data_ptr();
            let new_count = old_count.checked_add(1).unwrap();
            *(*counter).data_ptr() = new_count;
            //@ close Counter(k_counter)();
            //@ close Mutex_locked(k_counter, k_inv, frac, _);
            drop(guard);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req [1/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));
//@ ens true;
{
    let data = CountPulsesData { counter, source };
    //@ close count_pulses_pre(data);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        //@ let counter_ptr = Box::into_raw(Box::new(mutex));
        //@ close Counter(counter_ptr as *mut u32)();
        //@ close Mutex_full_borrow_content(counter_ptr as *mut u32, Counter(counter_ptr as *mut u32));
        //@ close Mutex(counter_ptr, Counter(counter_ptr as *mut u32));
        let counter = Box::into_raw(Box::new(mutex));
        //@ leak Mutex(counter, Counter(counter as *mut u32));

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let count;
            {
                let guard = (*counter).lock().unwrap();
                //@ open Mutex_locked(?k_counter, ?k_inv, ?frac, _);
                //@ open Counter(k_counter)();
                count = *(*counter).data_ptr();
                //@ close Counter(k_counter)();
                //@ close Mutex_locked(k_counter, k_inv, frac, _);
                drop(guard);
            }
            print_u32(count);
        }
    }
}