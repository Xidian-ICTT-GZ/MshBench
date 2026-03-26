use std::io::{stdin, stdout, Read, Write};

predicate block_of_bytes(ptr: *mut u8, len: usize) =
    match len {
        0 => true,
        _ => (*ptr |-> _) * block_of_bytes(unsafe { ptr.add(1) }, len - 1)
    };

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

#[requires(count > 0)]
#[ensures(block_of_bytes(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(block_of_bytes(start, count))]
#[ensures(block_of_bytes(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(unsafe { start.add(1) }, count - 1);
    }
}

#[requires(block_of_bytes(text, count) * block_of_bytes(key, count))]
#[ensures(block_of_bytes(text, count) * block_of_bytes(key, count))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(unsafe { text.add(1) }, unsafe { key.add(1) }, count - 1);
    }
}

#[requires(block_of_bytes(start, count))]
#[ensures(block_of_bytes(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(unsafe { start.add(1) }, count - 1);
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