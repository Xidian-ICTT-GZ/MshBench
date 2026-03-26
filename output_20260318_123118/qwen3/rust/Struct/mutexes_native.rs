#![feature(mutex_data_ptr)]

use std::sync::Mutex;

//@ pred_ctor Counter(counter: *mut u32)() = *counter |-> ?count;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T>(f: unsafe fn(arg: T), arg: T)
    where T: 'static
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
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

/*@ 

pred count_pulses_pre(data: CountPulsesData) =
    [1/3]Mutex_shared(data.counter, Counter(Mutex::data_ptr(data.counter)));

@*/

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
//@ req thread_token(?t) &*& count_pulses_pre(data);
//@ ens thread_token(t);
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, source} = data;

    loop {
        //@ inv thread_token(t) &*& [1/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));
        wait_for_pulse(source);
        //@ let k = begin_lifetime();
        {
            //@ let_lft 'a = k;
            let guard = (*counter).lock().unwrap();
            //@ open Mutex_locked(counter, _);
            //@ assert Counter(?ptr)();
            //@ open Counter(ptr)();
            let old_val = *ptr;
            let new_val = old_val.checked_add(1).unwrap();
            *ptr = new_val;
            //@ close Counter(ptr)();
            //@ close Mutex_locked(counter, Counter(ptr));
            drop(guard);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req [?f]Mutex_full(counter, Counter(Mutex::data_ptr(counter))) &*& f >= 2/3;
//@ ens [f]Mutex_full(counter, Counter(Mutex::data_ptr(counter)));
{
    let data = CountPulsesData { counter, source };
    //@ assert [f]Mutex_full(counter, ?P);
    //@ leak [f]Mutex_full(counter, P);
    //@ produce_lem_ptr_chunk fraction_leak(Mutex_full)(counter, P, f)() : [f]Mutex_full(counter, P) { 
    //@     open [f]Mutex_full(counter, P)();
    //@     close [f]Mutex_full(counter, P)();
    //@ } {
    //@     close [f]Mutex_full(counter, P)();
    //@ }
    //@ produce_lem_ptr_chunk fraction_split(Mutex_full)(counter, P, f, 1/3, f - 1/3)() : 
    //@     [1/3]Mutex_full(counter, P) &*& [f - 1/3]Mutex_full(counter, P) { 
    //@     open [f]Mutex_full(counter, P)();
    //@     close [1/3]Mutex_full(counter, P)();
    //@     close [f - 1/3]Mutex_full(counter, P)();
    //@ } {
    //@     open [1/3]Mutex_full(counter, P)();
    //@     open [f - 1/3]Mutex_full(counter, P)();
    //@     close [f]Mutex_full(counter, P)();
    //@ }
    //@ produce_lem_ptr_chunk shared_from_full(Mutex_full)(counter, P, 1/3)() : 
    //@     [1/3]Mutex_shared(counter, P) {
    //@     open [1/3]Mutex_full(counter, P)();
    //@     close [1/3]Mutex_shared(counter, P)();
    //@ } {
    //@     open [1/3]Mutex_shared(counter, P)();
    //@     close [1/3]Mutex_full(counter, P)();
    //@ }
    //@ produce_is_Spawnee(count_pulses, count_pulses_pre);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        let counter = Box::into_raw(Box::new(mutex));
        //@ let ptr = Mutex::data_ptr(counter);
        //@ close Counter(ptr)();
        //@ close Mutex_full(counter, Counter(ptr))();
        
        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let count;
            {
                let guard = (*counter).lock().unwrap();
                //@ open Mutex_locked(counter, _);
                //@ assert Counter(?ptr)();
                //@ open Counter(ptr)();
                count = *ptr;
                //@ close Counter(ptr)();
                //@ close Mutex_locked(counter, Counter(ptr));
                drop(guard);
            }
            print_u32(count);
        }
    }
}