use std::io::{stdin, stdout, Read, Write};
use std::ptr;

#[pred]
pub unsafe fn bytes(p: *mut u8, n: usize, xs: [u8]) = 
    n == xs.len() &&
    p != ptr::null_mut() &&
    (forall(|i: usize| (i < n) ==> (p.add(i) |-> xs[i])));

#[lemma]
#[requires(bytes(p, n, xs))]
#[ensures(bytes(p, n, xs))]
pub unsafe fn bytes_valid(p: *mut u8, n: usize, xs: &[u8]) {}

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[requires(std::alloc::Layout::from_size_align(count, 1).is_ok())]
#[ensures(bytes(result, count, ?xs))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    // We own uninitialized bytes: specify with arbitrary uninterpreted content
    // (The predicate requires knowledge of xs, so xs can be arbitrary here)
    result
}

#[requires(bytes(start, count, ?old_xs))]
#[requires(count > 0)]
#[ensures(bytes(start, count, ?new_xs))]
#[invariant(
    count > 0 &&
    (forall(|i: usize| i < (old_xs.len() - count) ==> start.add(i) |-> old_xs[i])) &&
    (start |-> ?b) 
)]
unsafe fn read_bytes(mut start: *mut u8, mut count: usize) {
    if count > 0 {
        // Consume ownership of start[0], read a byte into it, then recursively proceed
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(bytes(start, count, xs))]
#[requires(count > 0)]
#[ensures(bytes(start, count, xs))]
#[invariant(
    count > 0 &&
    (forall(|i: usize| i < (xs.len() - count) ==> start.add(i) |-> xs[i])) &&
    (start |-> xs[xs.len() - count])
)]
unsafe fn write_bytes(mut start: *mut u8, mut count: usize) {
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