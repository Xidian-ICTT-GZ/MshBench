use std::io::{stdin, stdout, Read, Write};

predicate buffer_owned(ptr: *mut u8, len: usize) = 
  ptr != std::ptr::null_mut() && len > 0;

predicate buffer_range(ptr: *mut u8, start: usize, end: usize) =
  start <= end;

#[requires(true)]
#[ensures(buffer_owned(result, 1))]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(buffer_owned(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(buffer_owned(start, count) && count > 0)]
#[ensures(buffer_owned(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        #[invariant(buffer_owned(start, count) && i <= count)]
        {
            if i == count {
                break;
            }
            let b = read_byte();

            *start.add(i) = b;

            i += 1;
        }
    }
}

#[requires(buffer_owned(start, count) && count > 0)]
#[ensures(buffer_owned(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        #[invariant(buffer_owned(start, count) && i <= count)]
        {
            if i == count {
                break;
            }

            let b = *start.add(i);

            write_byte(b);
            i += 1;
        }
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}