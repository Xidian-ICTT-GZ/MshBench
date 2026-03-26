#![feature(mutex_data_ptr)]

use std::sync::Mutex;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

/*@

predicate_ctor sendable_own<T>(t: T)() = t is T;

predicate mutex_own<T>(m: *mut Mutex<T>, v: T) = (*m) |-> ?inner &*& [_]mutex(m, inner, v);

lemma void create_mutex_own<T>(m: *mut Mutex<T>, v: T)
    requires (*m) |-> ?inner &*& struct_Mutex_padding(?padding),
    ensures mutex_own(m, v);
{
    close mutex(m, inner, v);
    leak mutex(m, inner, v);
    close mutex_own(m, v);
}

lemma void dispose_mutex_own<T>(m: *mut Mutex<T>)
    requires mutex_own(m, ?v),
    ensures (*m) |-> ?inner &*& struct_Mutex_padding(?padding);
{
    open mutex_own(m, v);
    close_struct(m);
}

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

#[requires(true)]
#[ensures(true)]
unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

/*@

predicate count_pulses_data(counter: *mut Mutex<u32>, source: i32) =
    mutex_own(counter, ?v) &*& source == source;

@*/

#[requires(count_pulses_data(counter, source))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;
    open count_pulses_data(counter, source);

    loop
        invariant mutex_own(counter, ?v),
        decreases _;
    {
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();
            let current = *(*counter).data_ptr();
            assert(current < u32::MAX);
            *(*counter).data_ptr() = current + 1;
            drop(guard);
        }
    }
}

#[requires(mutex_own(counter, ?v))]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };
    close count_pulses_data(counter, source);
    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);
        let counter = Box::into_raw(Box::new(mutex));
        create_mutex_own(counter, 0);

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop
            invariant mutex_own(counter, ?v),
            decreases _;
        {
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