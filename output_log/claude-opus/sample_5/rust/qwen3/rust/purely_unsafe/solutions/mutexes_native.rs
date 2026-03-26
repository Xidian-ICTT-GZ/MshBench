#![feature(mutex_data_ptr)]

use std::sync::Mutex;

#[pred]
struct MutexPred<T>(Box<Mutex<T>> mutex_box, *mut Mutex<T> mutex_ptr) =  
    mutex_box |-> ?mb &*&
    mutex_ptr == Box::into_raw(mutex_box) &*&
    mb@mutex^ mutex_ptr;

#[pred]
struct CountPulsesDataPred {
    counter: *mut Mutex<u32>,
    source: i32,
    mutex: Box<Mutex<u32>>,
} = 
    MutexPred(mutex, counter) &*&
    true; // source is an int, no heap ownership needed

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
    ensures
        CountPulsesDataPred { counter, source, mutex },
{
    // Construct predicate from ownership transfer
}

#[lemma]
fn count_pulses_data_pred_drop(data: CountPulsesDataPred)
    requires
        CountPulsesDataPred { counter, source: _, mutex } == data,
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
    CountPulsesDataPred { counter, source, mutex } == data
)]
#[ensures(
    MutexPred(mutex, counter)
)]
unsafe fn count_pulses(data: CountPulsesData) {
    let CountPulsesData { counter, source } = data;

    open CountPulsesDataPred(data);

    loop invariant
        CountPulsesDataPred { counter, source, mutex }
    {
        wait_for_pulse(source);

        {
            #[requires(
                MutexPred(mutex, counter)
            )]
            #[ensures(
                MutexPred(mutex, counter)
            )]
            let guard = (*counter).lock().unwrap();

            open MutexPred(mutex, counter);

            #[requires(
                *(*counter).data_ptr() |-> ?v &*& v < u32::MAX
            )]
            #[ensures(
                *(*counter).data_ptr() |-> (v + 1)
            )]
            {
                *(*counter).data_ptr() = v + 1;
            }

            close MutexPred(mutex, counter);

            drop(guard);
        }
    }
    close CountPulsesDataPred { counter, source, mutex };
}

#[requires(
    counter != 0 &&
    MutexPred(mutex, counter) &&
    source >= 0
)]
#[ensures(
    MutexPred(mutex, counter)
)]
unsafe fn count_pulses_async(counter: *mut Mutex<u32>, source: i32) {
    let mutex = Box::from_raw(counter);

    close CountPulsesDataPred { counter, source, mutex };

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
                    MutexPred(mutex, counter)
                )]
                #[ensures(
                    MutexPred(mutex, counter)
                )]
                let guard = (*counter).lock().unwrap();

                open MutexPred(mutex, counter);

                #[requires(
                    *(*counter).data_ptr() |-> ?v
                )]
                #[ensures(
                    *(*counter).data_ptr() |-> v
                )]
                count = *(*counter).data_ptr();

                close MutexPred(mutex, counter);

                drop(guard);
            }

            print_u32(count);
        }
    }
}