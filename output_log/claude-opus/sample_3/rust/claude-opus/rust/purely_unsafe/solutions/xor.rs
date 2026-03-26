use std::io::{stdin, stdout, Read, Write};

predicate u8s(ptr: *mut u8, count: usize; vs: seq<u8>) =
    count == 0 ?
        vs == seq_nil() && ptr as usize >= 0
    :
        *ptr |-> ?v &*& u8s(ptr.wrapping_add(1), count - 1, ?tail) &*& vs == seq_cons(v, tail);

unsafe fn read_byte() -> u8
    // No heap side effects directly
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    // No heap side effects directly
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0 ==> true)]
#[ensures(u8s(result, count, ?vs) &*& vs == seq_default(count, 0))]
unsafe fn alloc(count: usize) -> *mut u8;
    // Allocate memory for count bytes, all initialized to zero
    //
    // For VeriFast, we assume newly allocated memory contains zeros to satisfy ownership with known sequence.
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    // Initialize allocated memory with zeros to match ensured vs sequence of zeros
    for i in 0..count {
        *result.add(i) = 0;
    }
    result
}

#[requires(u8s(start, count, ?vs))]
#[ensures(u8s(start, count, ?rvs))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    // Consumes u8s for count bytes at start, returns fresh u8s with new contents
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(u8s(text, count, ?tvs) &*& u8s(key, count, ?kvs))]
#[ensures(u8s(text, count, ?rvs) &*& u8s(key, count, kvs) &*& rvs == xor_seq(tvs, kvs))]
predicate_family xor_seq(seq<u8> tvs, seq<u8> kvs) = 
    tvs == seq_nil() ? seq_nil() : seq_cons(seq_head(tvs) ^ seq_head(kvs), xor_seq(seq_tail(tvs), seq_tail(kvs)));

#[requires(u8s(text, count, ?tvs) &*& u8s(key, count, ?kvs))]
#[ensures(u8s(text, count, ?rvs) &*& u8s(key, count, kvs) &*& rvs == xor_seq(tvs, kvs))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
{
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    }
}

#[requires(u8s(start, count, ?vs))]
#[ensures(u8s(start, count, vs))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    // Consumes u8s with data vs -- then restores the same ownership predicate on exit
{
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