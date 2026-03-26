use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct BufPred<'a>(ptr: *mut u8, count: usize, data: &'a [u8]) =
    count > 0 ?
        ptr |-> ?b &*& BufPred(ptr.add(1), count - 1, &data[1..]) &*& b == data[0]
    :
        emp;

#[lemma]
#[requires(BufPred(p, n, data))]
#[ensures(BufPred(p.add(1), n - 1, &data[1..]))]
pub fn buf_pred_step(p: *mut u8, n: usize, data: &[u8]) {
    if n > 0 {
        open BufPred(p, n, data);
        close BufPred(p.add(1), n - 1, &data[1..]);
    }
}

#[pred]
pub struct AllocatedBuf(ptr: *mut u8, count: usize) =
    true == (count == 0)
  || (ptr |-> _ &*& AllocatedBuf(ptr.add(1), count - 1));

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
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, data))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        let rest_ptr = start.add(1);
        read_bytes(rest_ptr, count - 1);
        close BufPred(start, count, &[b][..].iter().chain(&std::slice::from_raw_parts(rest_ptr, count-1)).collect::<Vec<u8>>());
    } else {
        close BufPred(start, 0, &[]);
    }
}

#[requires(
    AllocatedBuf(text, count) *
    AllocatedBuf(key, count) *
    BufPred(text, count, ?text_data) *
    BufPred(key, count, ?key_data) &&
    text_data.len() == count &&
    key_data.len() == count
)]
#[ensures(
    AllocatedBuf(text, count) *
    AllocatedBuf(key, count) *
    BufPred(text, count, ?xor_data) *
    BufPred(key, count, key_data) &&
    xor_data.len() == count &&
    forall(|i: int| 0 <= i && (i as usize) < count ==> xor_data[i as usize] == text_data[i as usize] ^ key_data[i as usize])
)]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
        open BufPred(text, count, _);
        open BufPred(key, count, _);
        // form new xor_data vector logically
        close BufPred(text, count, &[t ^ k][..].iter().chain(&std::slice::from_raw_parts(text.add(1), count -1)).collect::<Vec<u8>>());
        close BufPred(key, count, key_data);
    } else {
        close BufPred(text, 0, &[]);
        close BufPred(key, 0, &[]);
    }
}

#[requires(AllocatedBuf(start, count) * BufPred(start, count, data) && data.len() == count)]
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, data))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    } else {
        // base case, do nothing
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