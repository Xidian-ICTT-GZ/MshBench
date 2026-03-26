use std::io::{stdin, stdout, Read, Write};

#[predicate]
fn bytes(start: *mut u8, count: usize) -> bool {
    count == 0 || exists(|v: u8| *start |-> v && bytes(start.add(1), count - 1))
}

#[predicate]
fn bytes_initialized(start: *mut u8, count: usize) -> bool {
    count == 0 || exists(|v: u8| *start |-> v && bytes_initialized(start.add(1), count - 1))
}

#[predicate]
fn bytes_owned(start: *mut u8, count: usize) -> bool {
    count == 0 || exists(|v: u8| *start |-> v && bytes_owned(start.add(1), count - 1))
}

#[requires(true)]
#[ensures(result == 0 || result == 1)]
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
#[ensures(bytes_owned(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(bytes(start, count))]
#[ensures(bytes_initialized(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(bytes_initialized(text, count) && bytes_initialized(key, count))]
#[ensures(bytes_initialized(text, count))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    }
}

#[requires(bytes_initialized(start, count))]
#[ensures(bytes_initialized(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
}

fn main() {
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
    }
}