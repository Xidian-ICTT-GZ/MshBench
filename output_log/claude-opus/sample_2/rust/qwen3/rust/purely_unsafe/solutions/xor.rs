use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct BytesPred(ptr: *mut u8, len: usize, data: seq<u8>) =
    len > 0 ?
        ptr |-> ?b &*&
        BytesPred(ptr.add(1), len - 1, seq_tail(data)) &*&
        head(data) == b
    :
        emp;

#[lemma]
#[requires(BytesPred(p, n, d))]
#[ensures(BytesPred(p, n, d))]
pub fn bytes_pred_valid(p: *mut u8, n: usize, d: seq<u8>) {}

#[pred]
pub struct AllocatedBytes(ptr: *mut u8, len: usize) =
    len > 0 ?
        ptr |-> _ &*&
        AllocatedBytes(ptr.add(1), len - 1)
    :
        emp;

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
    {
        let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
        let result = std::alloc::alloc(layout);
        if result.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        result
    }
}

unsafe fn read_bytes(start: *mut u8, count: usize) {
    #[requires(count >= 0 && AllocatedBytes(start, count))]
    #[ensures(AllocatedBytes(start, count) && BytesPred(start, count, ?d))]
    {
        if count > 0 {
            let b = read_byte();
            *start = b;
            read_bytes(start.add(1), count - 1);
            close BytesPred(start, count, cons(b, ?tail_d)) by {
                open BytesPred(start.add(1), count - 1, tail_d);
            }
        } else {
            close BytesPred(start, 0, nil);
        }
    }
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    #[requires(count >= 0 && AllocatedBytes(text, count) && AllocatedBytes(key, count) &&
                BytesPred(text, count, ?t) && BytesPred(key, count, ?k))]
    #[ensures(AllocatedBytes(text, count) && AllocatedBytes(key, count) &&
              BytesPred(text, count, seq_map(seq_range(0, count), |i| t[i] ^ k[i])) &&
              BytesPred(key, count, k))]
    {
        if count > 0 {
            open BytesPred(text, count, t);
            open BytesPred(key, count, k);
            let t0 = *text;
            let k0 = *key;
            *text = t0 ^ k0;
            xor_bytes(text.add(1), key.add(1), count - 1);
            open BytesPred(text.add(1), count - 1, ?t_tail);
            open BytesPred(key.add(1), count - 1, ?k_tail);
            close BytesPred(text, count, cons(t0 ^ k0, seq_map(seq_range(0, count - 1), |i| t_tail[i] ^ k_tail[i])));
            close BytesPred(key, count, cons(k0, k_tail));
        } else {
            close BytesPred(text, 0, nil);
            close BytesPred(key, 0, nil);
        }
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize) {
    #[requires(count >= 0 && AllocatedBytes(start, count) && BytesPred(start, count, ?d))]
    #[ensures(AllocatedBytes(start, count) && BytesPred(start, count, d))]
    {
        if count > 0 {
            open BytesPred(start, count, d);
            let b = *start;
            write_byte(b);
            write_bytes(start.add(1), count - 1);
            open BytesPred(start.add(1), count - 1, ?d_tail);
            close BytesPred(start, count, cons(b, d_tail));
        } else {
            close BytesPred(start, 0, nil);
        }
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