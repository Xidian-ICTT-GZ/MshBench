use std::alloc::{Layout, alloc, handle_alloc_error};

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn u32_owns(p: *mut u32) = 
  malloc_block(p, std::mem::size_of::<u32>());

#[predicate]
fn mutex_owns(p: *mut std::sync::Mutex<()>) = 
  malloc_block(p, std::mem::size_of::<std::sync::Mutex<()>>());

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
#[requires(true)]
#[ensures(true)]
{
  let package = Sendable { payload: arg };
  std::thread::spawn(move || {
    let package_moved = package;
    f(package_moved.payload)
  });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

unsafe fn create_mutex() -> *mut Mutex
#[requires(true)]
#[ensures(mutex_owns(result) &*& result != std::ptr::null_mut())]
{
  let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
  if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
  mutex.write(Mutex::new(()));
  mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
#[requires(mutex_owns(mutex))]
#[ensures(mutex_owns(mutex))]
{
  (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
#[requires(true)]
#[ensures(true)]
{
  drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
#[requires(true)]
#[ensures(true)]
{
  std::thread::sleep(std::time::Duration::from_millis(500));
}

unsafe fn print_u32(n: u32)
#[requires(true)]
#[ensures(true)]
{
  println!("{}", n);
}

struct CountPulsesData {
  counter: *mut u32,
  mutex: *mut Mutex,
  source: i32,
}

unsafe fn count_pulses(data: CountPulsesData)
#[requires(u32_owns(data.counter) &*& mutex_owns(data.mutex))]
#[ensures(false)]
{
  let CountPulsesData {counter, mutex, source} = data;
  loop {
    #[invariant(u32_owns(counter) &*& mutex_owns(mutex))]
    {
      wait_for_pulse(source);
      let guard = acquire(mutex);
      *counter = (*counter).checked_add(1).unwrap();
      release(guard);
    }
  }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
#[requires(u32_owns(counter) &*& mutex_owns(mutex))]
#[ensures(true)]
{
  let data = CountPulsesData { counter, mutex, source };
  spawn(count_pulses, data);
}

fn main()
#[requires(true)]
#[ensures(false)]
{
  unsafe {
    let counter = alloc(Layout::new::<u32>()) as *mut u32;
    if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
    *counter = 0;

    let mutex = create_mutex();
    count_pulses_async(counter, mutex, 1);
    count_pulses_async(counter, mutex, 2);
    loop {
      #[invariant(mutex_owns(mutex))]
      {
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        let count = *counter;
        release(guard);
        print_u32(count);
      }
    }
  }
}