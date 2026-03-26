use std::io::{stdin, stdout, Read, Write};

#[predicate]
pub struct BufPred<'a>(ptr: *mut u8, count: usize, data: &'a [u8]) =
    count == data.len() &*&
    count == 0 ? 
        true
    :
        ptr |-> ?v &*& BufPred(ptr.add(1), count - 1, &data[1..]) &*& v == data[0];

#[predicate]
pub struct AllocatedBuf(ptr: *mut u8, count: usize) =
    ptr != std::ptr::null_mut() &*&
    malloc_block(ptr, count);

#[lemma]
#[requires(BufPred(p, n, data))]
#[ensures(BufPred(p.add(1), n - 1, &data[1..]))]
pub fn buf_pred_step(p: *mut u8, n: usize, data: &[u8]) {
    // Provided predicate unfolding; no heap change
}

#[requires(std::alloc::Layout::from_size_align(count, 1).is_ok())]
#[ensures(AllocatedBuf(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(AllocatedBuf(start, count))]
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, ?data))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    } else {
        // count == 0, so BufPred for empty slice
    }
}

#[requires(AllocatedBuf(text, count) * AllocatedBuf(key, count) * BufPred(text, count, ?text_data) * BufPred(key, count, ?key_data))]
#[ensures(AllocatedBuf(text, count) * AllocatedBuf(key, count) * BufPred(text, count, xor_data) * BufPred(key, count, key_data))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    } else {
        // count == 0, predicates remain unchanged for empty buffers.
    }
}

#[requires(AllocatedBuf(start, count) * BufPred(start, count, ?data))]
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, data))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    } else {
        // count == 0, predicates remain for empty buffer
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
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
    }
}