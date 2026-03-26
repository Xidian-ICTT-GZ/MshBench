use std::io::{stdin, stdout, Read, Write};

#[predicate]
fn u8_slice(ptr: *mut u8, len: usize) -> bool {
    len == 0 || exists(|val: u8| ptr[0] == val && u8_slice(ptr.offset(1), len - 1))
}

#[predicate]
fn alloc_slice(ptr: *mut u8, len: usize) -> bool {
    len == 0 || (ptr != 0 && alloc_slice(ptr.offset(1), len - 1))
}

#[requires(alloc_slice(buf, 1))]
#[ensures(alloc_slice(buf, 1))]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(alloc_slice(buf, 1))]
#[ensures(alloc_slice(buf, 1))]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[ensures(result != 0 && alloc_slice(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(alloc_slice(start, count))]
#[ensures(alloc_slice(start, count) && u8_slice(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(alloc_slice(text, count) && u8_slice(text, count))]
#[requires(alloc_slice(key, count) && u8_slice(key, count))]
#[ensures(alloc_slice(text, count) && u8_slice(text, count))]
#[ensures(alloc_slice(key, count) && u8_slice(key, count))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    }
}

#[requires(alloc_slice(start, count) && u8_slice(start, count))]
#[ensures(alloc_slice(start, count) && u8_slice(start, count))]
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