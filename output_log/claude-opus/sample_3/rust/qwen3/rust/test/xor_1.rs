use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct BufPred<'a>(ptr: *mut u8, count: usize, data: &'a [u8]) =
    count == 0 ?
        true
    :
        // points-to predicate for the first byte and rest recursively
        ptr |-> data[0] &*& BufPred(ptr.add(1), count - 1, &data[1..]);

#[pred]
pub struct AllocatedBuf(ptr: *mut u8, count: usize) =
    // owns the allocated memory block, count bytes at ptr
    malloc_block(ptr, count);

#[lemma]
#[requires(BufPred(p, n, data))]
#[ensures(BufPred(p.add(1), n - 1, &data[1..]))]
pub fn buf_pred_step(p: *mut u8, n: usize, data: &[u8])
    requires n > 0 && data.len() >= n;
{
    open BufPred(p, n, data);
    close BufPred(p.add(1), n - 1, &data[1..]);
}

#[requires(std::alloc::Layout::from_size_align(count, 1).is_ok())]
#[ensures(AllocatedBuf(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    close AllocatedBuf(result, count);
    result
}

#[requires(AllocatedBuf(start, count))]
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, data))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    requires count >= 0;
    ensures exist<data: &[u8]> BufPred(start, count, data);
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        call read_bytes(start.add(1), count - 1);
        open BufPred(start.add(1), count - 1, _);
        close BufPred(start, count, &[b][..1] + &_);
    } else {
        close BufPred(start, 0, &[]);
    }
}

#[requires(AllocatedBuf(text, count) * AllocatedBuf(key, count) * BufPred(text, count, text_data) * BufPred(key, count, key_data))]
#[ensures(AllocatedBuf(text, count) * AllocatedBuf(key, count) * BufPred(text, count, xor_data) * BufPred(key, count, key_data))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
    requires count >= 0 && 
             forall<i: int> (0 <= i && i < count) ==> 
                 (_, _) -> (u8, u8); // implicit: arrays have length count
    ensures exists<xordata: &[u8]> BufPred(text, count, xordata) &*& BufPred(key, count, key_data) &*&
            forall<i: int> (0 <= i && i < count) ==> xordata[i] == text_data[i] ^ key_data[i];
{
    if count > 0 {
        open BufPred(text, count, text_data);
        open BufPred(key, count, key_data);
        let t = *text;
        let k = *key;
        *text = t ^ k;
        close BufPred(key, count - 1, &key_data[1..]);
        xor_bytes(text.add(1), key.add(1), count - 1);
        open BufPred(text.add(1), count - 1, _);
        close BufPred(text, count, &[t ^ k][..1] + &_);
        close BufPred(key, count, key_data);
    } else {
        close BufPred(text, 0, &[]);
        close BufPred(key, 0, &[]);
    }
}

#[requires(AllocatedBuf(start, count) * BufPred(start, count, data))]
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, data))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    requires count >= 0;
{
    if count > 0 {
        open BufPred(start, count, data);
        b = *start;
        write_byte(b);
        close BufPred(start.add(1), count - 1, &data[1..]);
        write_bytes(start.add(1), count - 1);
        close BufPred(start, count, data);
    } else {
        close BufPred(start, 0, &[]);
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