use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct bytes(p: *mut u8, n: usize, xs: [u8]) = 
    n == 0 ?
        p == std::ptr::null_mut() &*& xs == [] 
    :
        // points-to head byte and owns rest of array recursively
        p != std::ptr::null_mut() &*& p |-> xs[0] &*& bytes(p.offset(1), n - 1, tail(xs));

#[lemma]
#[requires(bytes(p, n, xs))]
#[ensures(bytes(p, n, xs))]
pub fn bytes_valid(p: *mut u8, n: usize, xs: &[u8]) {
    // Pure lemma, no heap changes
}

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(std::alloc::Layout::from_size_align(count, 1).is_ok())]
#[ensures(bytes(result, count, _))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    // We get full ownership of allocated block, bytes predicate with uninitialized values (_)
    result
}

#[requires(bytes(start, count, _))]
#[requires(count > 0)]
#[ensures(bytes(start, count, _))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        // Open predicate for first byte
        open bytes(start, count, _);
        let b = read_byte();
        *start = b;
        // Recursive call with tail slice
        read_bytes(start.add(1), count - 1);
        close bytes(start, count, _);
    }
}

#[requires(bytes(start, count, xs))]
#[requires(count > 0)]
#[ensures(bytes(start, count, xs))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        open bytes(start, count, xs);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        close bytes(start, count, xs);
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