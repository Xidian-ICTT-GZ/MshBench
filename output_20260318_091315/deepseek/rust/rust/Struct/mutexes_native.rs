#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ predicate Spawnee<T>(unsafe fn(T) f, predicate(T) pre) = true;

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

//@ predicate Counter(*mut u32 counter) = *counter |-> ?count;

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

/*@
predicate count_pulses_pre(CountPulsesData data) =
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
            //@ open Counter(Mutex::data_ptr(counter))();
            //@ let data_ptr = Mutex::data_ptr(counter);
            //@ assert *data_ptr |-> ?old_count;
            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();
            //@ assert *data_ptr |-> old_count + 1;
            //@ close Counter(Mutex::data_ptr(counter))();
            drop(guard);
        }
        //@ end_lifetime(k);
    }
}

//@ predicate_ctor Mutex_shared_ctor(*mut Mutex<u32> counter)() = [1/3]Mutex_shared(counter, Counter(Mutex::data_ptr(counter)));

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ req [?q]Mutex_shared(counter, Counter(Mutex::data_ptr(counter))) &*& q == 1/3;
//@ ens true;
{
    //@ close exists(predicate(CountPulsesData data) = [1/3]Mutex_shared(data.counter, Counter(Mutex::data_ptr(data.counter))));
    //@ close is_Spawnee(count_pulses, _);
    let data = CountPulsesData { counter, source };
    //@ close count_pulses_pre(data);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        //@ close Counter(Mutex::data_ptr(&mutex as *mut Mutex<u32>))();
        //@ close exists(Counter(Mutex::data_ptr(&mutex as *mut Mutex<u32>)));
        let counter = Box::into_raw(Box::new(mutex));
        //@ close Mutex_shared(counter, Counter(Mutex::data_ptr(counter)))();
        //@ split_fraction Mutex_shared(counter, Counter(Mutex::data_ptr(counter))), 1/3;
        //@ split_fraction Mutex_shared(counter, Counter(Mutex::data_ptr(counter))), 1/3;

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let count;
            {
                let guard = (*counter).lock().unwrap();
                //@ open Counter(Mutex::data_ptr(counter))();
                count = *(*counter).data_ptr();
                //@ close Counter(Mutex::data_ptr(counter))();
                drop(guard);
            }
            print_u32(count);
        }
    }
}