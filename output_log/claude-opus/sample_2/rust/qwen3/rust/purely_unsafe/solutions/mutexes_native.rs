#![feature(mutex_data_ptr)]

use std::sync::Mutex;

#[pred]
struct MutexPred<T>(Box<Mutex<T>>, *mut Mutex<T>) = 
    box_mutex: Box<Mutex<T>> &*& raw_ptr: *mut Mutex<T> &*&
    (box_mutex == Box::from_raw(raw_ptr)) &*& 
    raw_ptr != null &*&
    // Ownership of inner data protected by mutex
    mutex_internal(box_mutex);

#[pred]
mutex_internal<T>(Box<Mutex<T>> mutex) = mutex@; 
// This predicate captures ownership of mutex-protected data. 
// VeriFast models `mutex@` as the invariant/data protected inside mutex.

#[pred]
struct CountPulsesDataPred {
    counter: *mut Mutex<u32>,
    source: i32,
    mutex: Box<Mutex<u32>>,
} = 
    CountPulsesDataPred(counter, source, mutex) &*&
    MutexPred(mutex, counter) &*&
    source >= 0;

#[lemma]
fn mutex_pred_from_raw<T>(ptr: *mut Mutex<T>, box_val: Box<Mutex<T>>)
    requires
        ptr == Box::into_raw(box_val),
    ensures
        MutexPred(box_val, ptr),
{
    // VeriFast can derive this from the definition of Box::into_raw
}

#[lemma]
fn count_pulses_data_pred_new(counter: *mut Mutex<u32>, source: i32, mutex: Box<Mutex<u32>>)
    requires
        counter == Box::into_raw(mutex),
        source >= 0,
    ensures
        CountPulsesDataPred(counter, source, mutex),
{
    // Construct predicate from ownership transfer
}

#[lemma]
fn count_pulses_data_pred_drop(data: CountPulsesDataPred)
    requires
        data == CountPulsesDataPred(?counter, ?source, ?mutex),
    ensures
        MutexPred(mutex, counter),
{
    // Ownership returns to MutexPred on drop
}

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

unsafe fn wait_for_pulse(_source: i32) {
    std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32) {
    println!("{}", n);
}

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

struct CountPulsesData {
    counter: *mut Mutex<u32>,
    source: i32,
}

#[requires(
    CountPulsesDataPred(data.counter, data.source, ?mutex) == data &&
    MutexPred(mutex, data.counter)
)]
#[ensures(
    MutexPred(mutex, data.counter)
)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop {
        wait_for_pulse(source);

        {
            #[requires(
                MutexPred(?mutex_box, counter)
            )]
            #[ensures(
                MutexPred(mutex_box, counter)
            )]
            let guard = (*counter).lock().unwrap();

            // Here we describe ownership of the u32 inside data protected by mutex
            #[requires(
                guard@ == (*counter).data_ptr()@ &&
                guard |-> ?v &&
                v < u32::MAX
            )]
            #[ensures(
                guard |-> v + 1
            )]
            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            drop(guard);
        }
    }
}

#[requires(
    counter != null &&
    MutexPred(?mutex_box, counter) &&
    source >= 0
)]
#[ensures(
    MutexPred(mutex_box, counter)
)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let mutex = Box::from_raw(counter);
    count_pulses_data_pred_new(counter, source, mutex);

    let data = CountPulsesData { counter, source };

    spawn(count_pulses, data);
}

fn main() {
    unsafe {
        let mutex = Mutex::new(0u32);

        let counter = Box::into_raw(Box::new(mutex));

        mutex_pred_from_raw(counter, Box::new(mutex));

        count_pulses_async(counter, 1);
        count_pulses_async(counter, 2);

        loop {
            std::thread::sleep(std::time::Duration::from_millis(1000));

            let count;
            {
                #[requires(
                    MutexPred(?mutex_box, counter)
                )]
                #[ensures(
                    MutexPred(mutex_box, counter)
                )]
                let guard = (*counter).lock().unwrap();

                #[requires(
                    guard |-> ?v &&
                    v < u32::MAX
                )]
                #[ensures(
                    guard |-> v
                )]
                count = *(*counter).data_ptr();

                drop(guard);
            }

            print_u32(count);
        }
    }
}