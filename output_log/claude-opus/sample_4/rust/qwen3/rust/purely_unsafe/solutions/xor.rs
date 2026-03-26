use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct BytesPred(ptr: *mut u8, len: usize, data: seq<u8>) = 
    len > 0 
        ? (ptr |-> slice) &*& slice.length == len &*& slice.contents == data
        : ptr == std::ptr::null_mut() &*& data == seq![];

#[lemma]
#[requires(BytesPred(p, n, d))]
#[ensures(BytesPred(p, n, d))]
pub fn bytes_pred_valid(p: *mut u8, n: usize, d: seq<u8>) {}

#[pred]
pub struct AllocatedBytes(ptr: *mut u8, len: usize) =
    len > 0 ? (ptr |-> slice) &*& slice.length == len : ptr == std::ptr::null_mut();

#[lemma]
#[requires(AllocatedBytes(p, n))]
#[ensures(AllocatedBytes(p, n))]
pub fn allocated_bytes_valid(p: *mut u8, n: usize) {}

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
    #[requires(count > 0)]
    #[ensures(result != std::ptr::null_mut() && AllocatedBytes(result, count))]
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize) {
    #[requires(count >= 0 && AllocatedBytes(start, count))]
    #[ensures(AllocatedBytes(start, count) && BytesPred(start, count, ?d))]
    #[invariant(AllocatedBytes(start, count) && (count == 0 ? BytesPred(start, 0, seq![]) : true))]
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    #[requires(count >= 0 && AllocatedBytes(text, count) && AllocatedBytes(key, count) &&
                BytesPred(text, count, ?t) && BytesPred(key, count, ?k))]
    #[ensures(AllocatedBytes(text, count) && AllocatedBytes(key, count) &&
              BytesPred(text, count, seq_map(seq_range(0, count), |i| t[i] ^ k[i])) &&
              BytesPred(key, count, k))]
    #[invariant(AllocatedBytes(text, count) && AllocatedBytes(key, count) &&
                BytesPred(text, count, ?curr_t) && BytesPred(key, count, k))]
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize) {
    #[requires(count >= 0 && AllocatedBytes(start, count) && BytesPred(start, count, ?d))]
    #[ensures(AllocatedBytes(start, count) && BytesPred(start, count, d))]
    #[invariant(AllocatedBytes(start, count) && BytesPred(start, count, ?curr_d))]
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