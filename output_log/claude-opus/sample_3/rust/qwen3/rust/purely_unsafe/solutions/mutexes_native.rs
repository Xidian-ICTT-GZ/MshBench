#![feature(mutex_data_ptr)]

use std::sync::Mutex;

#[pred]
struct MutexPred<T>(Box<Mutex<T>>, *mut Mutex<T>) =
    mutex_box@ ==> true &*&
    box_unwrapped@ == mutex_box@ &*&
    // ownership of the Box<Mutex<T>>
    true &*&
    pointer(mutex_box@ as int, _) &*&
    // pointsto the raw pointer
    mutex_box == Box::from_raw(mutex_box as *mut _) &*&
    mutex_box.as_ref()@ && // abstract predicate for Mutex<T>
    true; // This is a placeholder to show ownership of the mutex, VeriFast would use the built-in predicates, but for explicitness we keep this form

#[pred]
struct CountPulsesDataPred {
    counter: *mut Mutex<u32>,
    source: i32,
    mutex: Box<Mutex<u32>>,
} = 
    MutexPred(mutex, counter) &*&
    pointer(counter as int, _) &*&
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
        CountPulsesDataPred { counter, source, mutex },
{
    // Ownership transfer from Box to CountPulsesDataPred
}

#[lemma]
fn count_pulses_data_pred_drop(data: CountPulsesDataPred)
    requires
        CountPulsesDataPred { counter, source: _, mutex } == data,
    ensures
        MutexPred(mutex, counter),
{
    // Ownership returned from CountPulsesDataPred to MutexPred on drop
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
                MutexPred(mutex, counter)
            )]
            #[ensures(
                MutexPred(mutex, counter)
            )]
            let guard = (*counter).lock().unwrap();

            #[requires(
                MutexPred(mutex, counter) &&
                guard@ == (*counter).data_ptr()@ &&
                guard |-> ?v &&
                v < u32::MAX
            )]
            #[ensures(
                MutexPred(mutex, counter) &&
                guard |-> v + 1
            )]
            *(*counter).data_ptr() = (*(*counter).data_ptr()).checked_add(1).unwrap();

            drop(guard);
        }
    }
}

#[requires(
    counter != 0 &&
    source >= 0 &&
    MutexPred(_, counter)
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