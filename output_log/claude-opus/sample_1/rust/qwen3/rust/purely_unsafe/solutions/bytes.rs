use std::io::{stdin, stdout, Read, Write};

#[predicate]
pub struct bytes(p: *mut u8, n: usize, xs: [u8]) = 
    n == length(xs) && p != std::ptr::null_mut() &*&
    (n == 0 ? true : p |-> ?v &*& bytes(p.add(1), n - 1, tail(xs)));

#[lemma]
#[requires(bytes(p, n, xs))]
#[ensures(bytes(p, n, xs))]
pub fn bytes_valid(p: *mut u8, n: usize, xs: [u8]) {}

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count >= 0)]
#[ensures(bytes(result, count, ?xs))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    // Init new memory with uninitialized bytes, we frame arbitrary values xs of length count
    // so result points to bytes(result, count, xs)
    result
}

#[requires(bytes(start, count, _xs))]
#[requires(count > 0)]
#[ensures(bytes(start, count, ?ys))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        // After recursive call, bytes(start+1, count-1, ys') for some ys'
        read_bytes(start.add(1), count - 1);
        // Frame the full bytes predicate for combined slice
        // bytes(start, count, [b] + ys')
        close bytes(start, count, cons(b, ?ys'));
    }
}

#[requires(bytes(start, count, ?xs))]
#[requires(count > 0)]
#[ensures(bytes(start, count, xs))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
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