use std::io::{Read, Write, stdin, stdout};

predicate byte_array(void* start, usize count, list<u8> bytes) =
    count == 0 ?
        emp
    :
        start |-> ?b &*&
        byte_array(start + 1, count - 1, tail(bytes)) &*&
        b == head(bytes);

#[requires(true)]
#[ensures(result != 0)]
unsafe fn read_byte() -> u8
    
;

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8)
    
;

unsafe fn alloc(count: usize)
    #[requires(count > 0)]
    #[ensures(result != 0)]
    #[ensures(byte_array(result, count, ?bs) &*& length(bs) == count)]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    
    
    
    assume(byte_array(result, count, replicate(count, 0)));
    result
}

#[requires(byte_array(start, count, ?bs))]
#[ensures(byte_array(start, count, bs))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    requires true
{
    if count > 0 {
        let b = read_byte();
        
        close exists(bs0, bs1).(bs == Cons(bs0, bs1));
        *start = b;
        consume exists(bs0, bs1).(bs == Cons(bs0, bs1));
        read_bytes(start.add(1), count - 1);
    }
    close byte_array(start, count, bs);
}

#[requires(byte_array(text, count, ?tb) &*& byte_array(key, count, ?kb))]
#[ensures(byte_array(text, count, ?new_tb) &*& byte_array(key, count, kb) &*& length(new_tb) == count)]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
{
    if count > 0 {
        open byte_array(text, count, ?tb);
        open byte_array(key, count, ?kb);
        let t = *text;
        let k = *key;
        let x = t ^ k;
        *text = x;
        close byte_array(text + 1, count - 1, tail(tb));
        close byte_array(key + 1, count - 1, tail(kb));
        xor_bytes(text.add(1), key.add(1), count - 1);
        close byte_array(text, count, cons(x, tail(tb)));
        close byte_array(key, count, kb);
    }
}

#[requires(byte_array(start, count, ?bs))]
#[ensures(byte_array(start, count, bs))]
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        open byte_array(start, count, ?bs);
        let b = *start;
        close byte_array(start + 1, count - 1, tail(bs));
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        close byte_array(start, count, bs);
    }
}

fn main()
{
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
        
    }
}

fixpoint list<u8> replicate(usize n, u8 v) {
    return n == 0 ? nil : cons(v, replicate(n - 1, v));
}

predicate byte_array(void* start, usize count, list<u8> bytes);

fixpoint u8 head(list<u8> xs) {
    switch(xs) {
        case nil: return 0;
        case cons(x, _): return x;
    }
}

fixpoint list<u8> tail(list<u8> xs) {
    switch(xs) {
        case nil: return nil;
        case cons(_, xs1): return xs1;
    }
}

fixpoint list<u8> cons(u8 x, list<u8> xs) {
    return [x] + xs;
}