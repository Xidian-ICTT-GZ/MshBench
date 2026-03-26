use std::io::{stdin, stdout, Read, Write};

pred u8s(ptr: *mut u8, count: usize) = 
    count == 0 ? 
        true 
    : 
        *ptr |-> _ &*& u8s(ptr.add(1), count - 1);

pred u8s_val(ptr: *mut u8, count: usize; vals: list<u8>) = 
    count == 0 ? 
        vals == nil 
    : 
        *ptr |-> ?v &*& u8s_val(ptr.add(1), count - 1, ?rest) &*& vals == cons(v, rest);

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

#[requires(count > 0)]
#[ensures(u8s(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(u8s(start, count))]
#[ensures(u8s_val(start, count, ?vals))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    } else {
        // zero-length base case: no heap changes, preserves u8s_val with nil
        // We specify u8s_val with vals == nil
        // but since count==0, vals==nil holds trivially
    }
}

#[requires(u8s_val(text, count, ?tvals) &*& u8s_val(key, count, ?kvals))]
#[ensures(u8s_val(text, count, zip_with_xor(tvals, kvals)) &*& u8s_val(key, count, kvals))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    } else {
        // base case: count==0, nothing to do, preserves vals
    }
}

fixpoint list<u8> zip_with_xor(list<u8> xs, list<u8> ys) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0):
            switch (ys) {
                case nil: return nil;
                case cons(y0, ys0):
                    return cons(x0 ^ y0, zip_with_xor(xs0, ys0));
            }
    }
}

#[requires(u8s_val(start, count, ?vals))]
#[ensures(u8s_val(start, count, vals))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    } else {
        // base case count==0: preserves heap and vals
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