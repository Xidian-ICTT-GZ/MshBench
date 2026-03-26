use std::io::{stdin, stdout, Read, Write};

predicate u8s(ptr: *mut u8, count: usize; vs: seq<u8>) =
    count == 0 ?
        vs == seq_nil() &*& ptr as usize >= 0
    :
        *ptr |-> ?v &*& u8s(ptr.wrapping_add(1), count - 1, ?tail) &*& vs == seq_cons(v, tail);

unsafe fn read_byte()
    #[ensures(result |-> ?v)]
    -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    #[requires(value |-> _)]
    #[ensures(true)]
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[ensures(u8s(result, count, ?vs))]
unsafe fn alloc(count: usize)
    -> *mut u8
    // Allocation yields full ownership of count bytes of u8s with unknown contents vs
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(u8s(start, count, _))]
#[ensures(u8s(start, count, _))]
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(u8s(text, count, ?tvs) &*& u8s(key, count, ?kvs))]
#[ensures(u8s(text, count, map(tvs, (|x, i| x ^ seq_index(kvs, i)))) &*& u8s(key, count, kvs))]
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