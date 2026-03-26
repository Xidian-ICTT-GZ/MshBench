use std::io::{stdin, stdout, Read, Write};
use std::alloc::{alloc, handle_alloc_error, Layout};

pred u8s(ptr: *mut u8, count: usize) = 
    count == 0 ? 
        emp 
    : 
        *ptr |-> _ &*& u8s(ptr.add(1), count - 1);

pred u8s_val(ptr: *mut u8, count: usize; vals: list<u8>) = 
    count == 0 ? 
        emp &*& vals == nil 
    : 
        *ptr |-> ?v &*& u8s_val(ptr.add(1), count - 1, ?rest) &*& vals == cons(v, rest);

#[requires(true)]
#[ensures(result |-> _)]
unsafe fn read_byte() -> u8
    //@ requires emp;
    //@ ensures result |-> _;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(value |-> _)]
#[ensures(emp)]
unsafe fn write_byte(value: u8)
    //@ requires value |-> _;
    //@ ensures emp;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(u8s(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
    //@ requires count > 0;
    //@ ensures u8s(result, count);
{
    let layout = Layout::from_size_align(count, 1).unwrap();
    let result = alloc(layout);
    if result.is_null() {
        handle_alloc_error(layout);
    }
    result
}

#[requires(u8s(start, count))]
#[ensures(u8s_val(start, count, ?vals))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    //@ requires u8s(start, count);
    //@ ensures u8s_val(start, count, vals);
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    } else {
        // zero count means no heap
    }
}

#[requires(u8s_val(text, count, ?tvals) &*& u8s_val(key, count, ?kvals))]
#[ensures(u8s_val(text, count, xor_lists(tvals, kvals)) &*& u8s_val(key, count, kvals))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
    //@ requires u8s_val(text, count, ?tvals) &*& u8s_val(key, count, ?kvals);
    //@ ensures u8s_val(text, count, xor_lists(tvals, kvals)) &*& u8s_val(key, count, kvals);
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
unsafe fn write_bytes(start: *mut u8, count: usize)
    //@ requires u8s_val(start, count, ?vals);
    //@ ensures u8s_val(start, count, vals);
{
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
}

// predicate for ownership of a single u8 value
predicate u8_val(loc: *mut u8, v: u8) = loc |-> v;

// lemma for xor of two lists element-wise
fixpoint list<u8> xor_lists(list<u8> xs, list<u8> ys) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): 
            switch (ys) {
                case nil: return nil;
                case cons(y, ys0): return cons(x ^ y, xor_lists(xs0, ys0));
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