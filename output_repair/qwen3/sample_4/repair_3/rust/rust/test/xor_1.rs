use std::io::{stdin, stdout, Read, Write};

predicate u8_slice(*mut u8 ptr, usize len) =
    match len {
        0 => emp,
        _ => *ptr |-> _ &*& u8_slice(ptr.offset(1), len - 1)
    };

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(u8_slice(start, count))]
#[ensures(u8_slice(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.offset(1), count - 1);
    }
}

#[requires(u8_slice(text, count) &*& u8_slice(key, count))]
#[ensures(u8_slice(text, count) &*& u8_slice(key, count))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.offset(1), key.offset(1), count - 1);
    }
}

#[requires(u8_slice(start, count))]
#[ensures(u8_slice(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.offset(1), count - 1);
    }
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        std::alloc::assume_allocated(text as *mut u8, 10);
        std::alloc::assume_allocated(key as *mut u8, 10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
    }
}