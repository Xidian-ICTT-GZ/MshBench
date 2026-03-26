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
            //@ open Mutex_locked(counter, _);
            //@ open Counter(?ptr)();
            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();
            //@ close Counter(ptr)();
            //@ close Mutex_locked(counter, _);
            drop(guard);
        }
        
        
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req [?q]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));
//@ ens [q]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));
{
    let data = CountPulsesData { counter, source };
    //@ close count_pulses_pre(data);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        
        let counter = Box::into_raw(Box::new(mutex));
        //@ close Counter(Mutex::data_ptr(counter))();
        //@ close Mutex_full_borrow_content(counter, Counter(Mutex::data_ptr(counter)))();
        //@ close Mutex(counter, _);
        //@ leak Mutex(counter, _) &*& full_borrow(_, Mutex_full_borrow_content(counter, Counter(Mutex::data_ptr(counter))));
        //@ produce_lem_ptr_chunk full_borrow(_, Mutex_full_borrow_content(counter, Counter(Mutex::data_ptr(counter))))() { close Mutex_full_borrow_content(counter, Counter(Mutex::data_ptr(counter)))(); };

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            
            std::thread::sleep(std::time::Duration::from_millis(1000));
            
            let count;
            {
                
                let guard = (*counter).lock().unwrap();
                //@ open Mutex_locked(counter, _);
                //@ open Counter(?ptr)();
                count = *(*counter).data_ptr();
                //@ close Counter(ptr)();
                //@ close Mutex_locked(counter, _);
                drop(guard);
            }
            
            
            print_u32(count);
        }
    }
}