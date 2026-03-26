use std::io::{stdin, stdout, Read, Write};

#[pred]
pub unsafe fn bytes(p: *mut u8, n: usize, xs: [u8]) = 
    n > 0 ?
      p |-> xs[0] * bytes(p.add(1), n - 1, xs[1..]) 
    : n == 0 &*& xs.len == 0;

#[lemma]
#[requires(bytes(p, n, xs))]
#[ensures(bytes(p, n, xs))]
pub fn bytes_valid(p: *mut u8, n: usize, xs: &[u8]) {}

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
    result
}

#[requires(bytes(start, count, xs))]
#[requires(count > 0)]
#[ensures(bytes(start, count, _))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(bytes(start, count, xs))]
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