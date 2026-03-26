use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct BufPred<'a>(ptr: *mut u8, count: usize, data: &'a [u8]) =
    count > 0 &*&
    ptr |-> ?v &*&
    data[0] == v &*&
    BufPred(ptr.add(1), count - 1, &data[1..]) 
    || (count == 0 &*& emp);

#[lemma]
#[requires(BufPred(p, n, data))]
#[ensures((n > 0 ==> BufPred(p.add(1), n - 1, &data[1..])) && (n == 0 ==> emp))]
pub fn buf_pred_step(p: *mut u8, n: usize, data: &[u8]) {
    if n > 0 {
        open BufPred(p, n, data);
        close BufPred(p.add(1), n - 1, &data[1..]);
    }
}

#[pred]
pub struct AllocatedBuf(ptr: *mut u8, count: usize) =
    ptr |-> _ &*&
    allocated(ptr, count);

#[predicate]
pub predicate allocated(ptr: *mut u8, count: usize) =
    count == 0 ? emp : ptr |-> _ &*& allocated(ptr.add(1), count - 1);

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
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, old(?data)))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    } else {
        // Base case: count == 0
    }
}

#[requires(AllocatedBuf(text, count) * AllocatedBuf(key, count)
    * BufPred(text, count, text_data) * BufPred(key, count, key_data))]
#[ensures(AllocatedBuf(text, count) * AllocatedBuf(key, count)
    * BufPred(text, count, xor_data) * BufPred(key, count, key_data)
    && forall<int i>(0 <= i && i < count ==> xor_data[i] == text_data[i] ^ key_data[i]))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        open BufPred(text, count, ?text_data);
        open BufPred(key, count, ?key_data);

        let t = *text;
        let k = *key;
        *text = t ^ k;

        xor_bytes(text.add(1), key.add(1), count - 1);

        close BufPred(text, count, ?xor_data);
        close BufPred(key, count, key_data);
    } else {
        // Base case: count == 0
    }
}

#[requires(AllocatedBuf(start, count) * BufPred(start, count, data))]
#[ensures(AllocatedBuf(start, count) * BufPred(start, count, data))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        open BufPred(start, count, ?data);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        close BufPred(start, count, data);
    } else {
        // Base case: count == 0
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