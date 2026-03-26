#![feature(mutex_data_ptr)]

use std::sync::Mutex;

predicate mutex_u32(m: *mut Mutex<u32>, v: u32) =
    (*m).Mutex(v);

predicate counter_shared(counter: *mut Mutex<u32>) =
    [1/2](*counter).Mutex(?v);

predicate sendable<T>(s: Sendable<T>, payload: T) =
    s.payload |-> payload;

predicate count_pulses_data(d: CountPulsesData, counter: *mut Mutex<u32>, source: i32) =
    d.counter |-> counter &*& d.source |-> source &*& counter_shared(counter);

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[requires(true)]
#[ensures(true)]
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

#[predicate]
fn mutex_guard(counter: *mut Mutex<u32>, v: u32) =
    (*counter).Mutex(v);

#[requires(count_pulses_data(data, ?counter, ?source))]
#[ensures(false)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop
    #[invariant([
        counter_shared(counter),
        (*counter).Mutex(?v)
    ])]
    {
        wait_for_pulse(source);

        {
            let guard = (*counter).lock().unwrap();
            // The lock returns MutexGuard owning full ownership of the mutex data,
            // so we open mutex for v, then close it after increment.

            // Open mutex to get full ownership
            open mutex_u32(counter, ?old_v);
            close mutex_u32(counter, old_v);

            // Because we only have half ownership in counter_shared,
            // but locking gives full ownership temporarily,
            // we can open and close, which VeriFast supports.

            // Actually, to be precise:
            // lock returns MutexGuard with full ownership, so the predicate mutex_u32
            // here must denote that – so open it, then update the data,
            // then close with new value.

            open mutex_u32(counter, old_v);
            let new_v = old_v + 1;
            close mutex_u32(counter, new_v);

            // Counter_shared keeps half ownership (1/2), MutexGuard owns full ownership (1),
            // so opening and closing is balanced.

            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            drop(guard);
        }
    }
}

#[requires(counter_shared(counter))]
#[ensures(true)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let data = CountPulsesData { counter, source };

    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0);

        #[predicate]
        fn mutex_init(m: *mut Mutex<u32>, v: u32) =
            (*m).Mutex(v);

        let counter = Box::into_raw(Box::new(mutex));

        // After allocation, we have full ownership of mutex predicate.
        open mutex_u32(counter, 0);
        close counter_shared(counter);
        close counter_shared(counter);

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop
        #[invariant(counter_shared(counter))]
        {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                let guard = (*counter).lock().unwrap();

                open mutex_u32(counter, ?v);
                count = v;
                close mutex_u32(counter, v);

                drop(guard);
            }

            print_u32(count);
        }
    }
}