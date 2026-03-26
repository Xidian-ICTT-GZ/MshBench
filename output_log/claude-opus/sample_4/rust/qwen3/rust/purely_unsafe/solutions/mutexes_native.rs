#![feature(mutex_data_ptr)]

use std::sync::Mutex;

#[pred]
struct MutexPred<T>(Box<Mutex<T>>, *mut Mutex<T>) = 
    // Own the box pointing to the mutex, and full ownership of the Mutex<T> it points to
    // VeriFast ownership of Box (heap allocation)
    Box_own(mut bx) &*& 
    // VeriFast ownership of the underlying mutex data
    mutex_mut(&*bx, ptr);

#[pred]
struct CountPulsesDataPred {
    counter: *mut Mutex<u32>,
    source: i32,
    mutex: Box<Mutex<u32>>,
} =
    // Own the Box<Mutex<u32>> and heap ownership of the mutex pointed by counter
    MutexPred(mutex, counter) &*&
    // Pure value ownership of source
    true;

#[lemma]
fn mutex_pred_from_raw<T>(ptr: *mut Mutex<T>, box_val: Box<Mutex<T>>)
    requires
        ptr == Box::into_raw(box_val),
    ensures
        MutexPred(box_val, ptr),
{
    // VeriFast derives ownership transfer from Box::into_raw
}

#[lemma]
fn count_pulses_data_pred_new(counter: *mut Mutex<u32>, source: i32, mutex: Box<Mutex<u32>>)
    requires
        counter == Box::into_raw(mutex),
    ensures
        CountPulsesDataPred { counter, source, mutex },
{
    // Construct CountPulsesDataPred owning mutex and counter
    mutex_pred_from_raw(counter, mutex);
}

#[lemma]
fn count_pulses_data_pred_drop(data: CountPulsesDataPred)
    requires
        CountPulsesDataPred { counter, source: _, mutex } == data,
    ensures
        MutexPred(mutex, counter),
{
    // On drop, return full MutexPred ownership
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
    CountPulsesDataPred { counter, source, mutex } == data
)]
#[ensures(
    MutexPred(mutex, counter)
)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    loop {
        wait_for_pulse(source);

        {
            #[requires(
                MutexPred(_, counter)
            )]
            #[ensures(
                MutexPred(_, counter)
            )]
            let guard = (*counter).lock().unwrap();

            #[requires(
                guard@ == (*counter).data_ptr()@ &&
                guard |-> ?v
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
    counter != 0 &&
    MutexPred(_, counter) &&
    source >= 0
)]
#[ensures(
    MutexPred(_, counter)
)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let mutex = Box::from_raw(counter);
    let data = CountPulsesData { counter, source };

    count_pulses_data_pred_new(counter, source, mutex);

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
                    MutexPred(_, counter)
                )]
                #[ensures(
                    MutexPred(_, counter)
                )]
                let guard = (*counter).lock().unwrap();

                #[requires(
                    guard |-> ?v
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