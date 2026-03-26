#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@ 
pred_ctor Spawnee<T>(f: unsafe fn(T), pre: pred<T>)() = 
    forall<t>. pre(t) ==> 
        exists<post>. call(f)(t, post) &*& post();
@*/

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

/*@ 
pred wait_for_pulse_ghost(source: i32) = true;
@*/

unsafe fn wait_for_pulse(_source: i32)
//@ req wait_for_pulse_ghost(?s);
//@ ens wait_for_pulse_ghost(s);
{
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
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

pred count_pulses_post(data: CountPulsesData) =
    [1/3]Mutex_shared(data.counter, Counter(Mutex::data_ptr(data.counter)));

lemma void count_pulses_ensures()
    requires count_pulses_pre(?data);
    ensures count_pulses_post(data);
{
    open count_pulses_pre(data);
    close count_pulses_post(data);
}

@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ req thread_token(?t) &*& count_pulses_pre(data);
//@ ens thread_token(t);
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, source} = data;

    loop {
        //@ inv thread_token(t) &*& [1/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter))) &*& wait_for_pulse_ghost(source);
        wait_for_pulse(source);
        //@ close wait_for_pulse_ghost(source);
        {
            let guard = (*counter).lock().unwrap();
            //@ open Mutex_locked(counter, _);
            //@ open Counter(?c_ptr)();
            let old_val = *c_ptr;
            let new_val = old_val.checked_add(1).unwrap();
            *c_ptr = new_val;
            //@ close Counter(c_ptr)();
            //@ close Mutex_locked(counter, Counter(c_ptr));
            drop(guard);
        }
    }
}

/*@ 

pred count_pulses_async_pre(counter: *mut Mutex<u32>, source: i32) =
    [2/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));

pred count_pulses_async_post(counter: *mut Mutex<u32>, source: i32) =
    [2/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));

lemma void split_mutex()
    requires Mutex_full(?m, Counter(?p)) &*& full_permission(?frac);
    ensures [frac]Mutex_shared(m, Counter(p)) &*& [1-frac]Mutex_shared(m, Counter(p));
{
    open Mutex_full(m, _);
    assert p == Mutex::data_ptr(m);
    close Mutex_shared(m, Counter(p));
    close Mutex_shared(m, Counter(p));
    leak [frac]Mutex_shared(m, Counter(p));
    leak [1-frac]Mutex_shared(m, Counter(p));
}

lemma void join_mutex()
    requires [?f1]Mutex_shared(?m, Counter(?p)) &*& [?f2]Mutex_shared(m, Counter(p)) &*& f1 + f2 == 1;
    ensures Mutex_full(m, Counter(p));
{
    close Mutex_full(m, Counter(p));
}

@*/

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req count_pulses_async_pre(counter, source);
//@ ens count_pulses_async_post(counter, source);
{
    let data = CountPulsesData { counter, source };
    //@ close count_pulses_pre(data);
    //@ produce_lem_ptr_chunk(count_pulses_ensures)() : count_pulses_post(data);
    //@ produce_type_interp(Spawnee(count_pulses, count_pulses_pre));
    spawn(count_pulses, data);
    //@ open count_pulses_post(data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        //@ close Counter(&mutex as *const _ as *mut u32)();
        //@ close Mutex_full(&mutex as *const _ as *mut Mutex<u32>, Counter(&mutex as *const _ as *mut u32));
        let counter = Box::into_raw(Box::new(mutex));
        //@ assert Mutex_full(counter, Counter(?p));
        //@ split_mutex();
        //@ leak [1/3]Mutex_shared(counter, Counter(p));
        
        count_pulses_async(counter, 1);
        //@ open count_pulses_async_post(counter, 1);
        count_pulses_async(counter, 2);
        //@ open count_pulses_async_post(counter, 2);

        loop {
            //@ inv [1/3]Mutex_shared(counter, Counter(p));
            std::thread::sleep(std::time::Duration::from_millis(1000));
            
            let count;
            {
                let guard = (*counter).lock().unwrap();
                //@ open Mutex_locked(counter, _);
                //@ open Counter(p)();
                count = *p;
                //@ close Counter(p)();
                //@ close Mutex_locked(counter, Counter(p));
                drop(guard);
            }
            print_u32(count);
        }
    }
}