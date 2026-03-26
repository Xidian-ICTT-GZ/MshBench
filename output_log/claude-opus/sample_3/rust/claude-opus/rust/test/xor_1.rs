use std::io::{stdin, stdout, Read, Write};
use std::alloc::{alloc, Layout};

pred u8s(ptr: *mut u8, count: usize) = 
    count == 0 ? 
        emp 
    : 
        ptr |-> _ &*& u8s(ptr.add(1), count - 1);

pred u8s_val(ptr: *mut u8, count: usize; vals: list<u8>) = 
    count == 0 ? 
        emp &*& vals == nil 
    : 
        ptr |-> ?v &*& u8s_val(ptr.add(1), count - 1, ?rest) &*& vals == cons(v, rest);

#[requires(true)]
#[ensures(result |-> _)]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(value |-> _)]
#[ensures(emp)]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(result |-> _ &*& u8s(result, count - 1))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = Layout::from_size_align(count, 1).unwrap();
    let result = alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(u8s(start, count))]
#[ensures(u8s_val(start, count, _))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(u8s_val(text, count, ?tvals) &*& u8s_val(key, count, ?kvals))]
#[ensures(u8s_val(text, count, ?xored))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
    //@ requires u8s_val(text, count, tvals) &*& u8s_val(key, count, kvals);
    //@ ensures u8s_val(text, count, xored) &*& u8s_val(key, count, kvals);
    //@ requires forall (int i) :: 0 <= i < count ==> xored[i] == tvals[i] ^ kvals[i];
{
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    }
}

#[requires(u8s_val(start, count, ?vals))]
#[ensures(u8s_val(start, count, vals))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
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