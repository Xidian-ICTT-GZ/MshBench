use std::io::{stdin, stdout, Read, Write};

predicate bytes_slice(*mut u8 start, usize len) =
    if len == 0 then emp else
        *start |-> _ &*& bytes_slice(start.offset(1), len - 1);

#[requires(true)]
#[ensures(bytes_slice(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(bytes_slice(start, count))]
#[ensures(bytes_slice(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        if i == count {
            break;
        }
        #[invariant(bytes_slice(start, i) &*& bytes_slice(start.offset(i as isize), count - i))]
        {
            let b = read_byte();
            *start.add(i) = b;
            i += 1;
        }
    }
}

#[requires(bytes_slice(start, count))]
#[ensures(bytes_slice(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        if i == count {
            break;
        }
        #[invariant(bytes_slice(start, i) &*& bytes_slice(start.offset(i as isize), count - i))]
        {
            write_byte(*start.add(i));
            i += 1;
        }
    }
}

#[requires(true)]
#[ensures(true)]
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

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}