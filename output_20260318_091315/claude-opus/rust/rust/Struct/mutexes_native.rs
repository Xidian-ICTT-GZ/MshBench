#![feature(mutex_data_ptr)]

use std::sync::Mutex;

/*@

predicate Counter(u: u32; counter: *mut u32) = counter->?v &*& v == u;

predicate_ctor MutexInvariant(counter: *mut u32)(mutex: &Mutex<u32>) =
    mutex.get_mut_ghost() &*&
    // ownership of the u32 inside Mutex, permission is full since we open/close fully
    counter->_ &*& true;

predicate Mutex_shared(mutex: *mut Mutex<u32>, inv: predicate(&Mutex<u32>)) =
    mutex->?mutex_val &*& inv(&*mutex_val);

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T>(f: unsafe fn(arg: T), arg: T)
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

//@ pred_ctor Counter(counter: *mut u32)() = *counter |-> ?count;

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

/*@

predicate count_pulses_pre(data: CountPulsesData) =
    [1/3]Mutex_shared(data.counter, (|m: &Mutex<u32>| true));

@*/

unsafe fn count_pulses(data: CountPulsesData)
//@ requires thread_token(currentThread) &*& count_pulses_pre(data);
//@ ensures thread_token(currentThread);
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, source} = data;

    loop {
        //@ invariant thread_token(currentThread) &*& [1/3]Mutex_shared(counter, (|m: &Mutex<u32>| true));
        wait_for_pulse(source);
        //@ let k = begin_lifetime();
        {
            //@ let_lft 'a = k;
            let guard = (*counter).lock().unwrap();

            
            unsafe {
                let data_ptr = (*counter).data_ptr();
                let old_count = *data_ptr;
                let new_count = old_count.checked_add(1).unwrap();
                *data_ptr = new_count;
            }

            drop(guard);
        }
    }
}

unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32)
//@ requires true;
//@ ensures true;
{
    let data = CountPulsesData { counter, source };
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        let counter = Box::into_raw(Box::new(mutex));

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
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