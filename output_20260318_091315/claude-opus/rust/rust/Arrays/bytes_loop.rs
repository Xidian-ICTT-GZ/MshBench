use std::io::{Read, Write, stdin, stdout};

predicate byte_slice(char *start, int count, list<u8> bytes) =
    count == 0 ?
        start == 0
    :
        start != 0 &*&
        chars(start, 1, cons(?b, ?rest)) &*& byte_slice(start + 1, count - 1, rest) &*&
        bytes == cons(b, rest);

predicate chars(char *ptr, int n, list<u8> cs) =
    n == 0 ?
        ptr == 0
    :
        ptr != 0 &*&
        ptr |-> ?c &*& chars(ptr + 1, n - 1, ?rest) &*&
        cs == cons(c, rest);

#[requires(true)]
#[ensures(result == ?b)]
unsafe fn read_byte() -> u8
    //@ requires true;
    //@ ensures byte_slice(?p, 1, ?l) &*& l == cons(result, nil);
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8)
    //@ requires chars(?p, 1, cons(value, nil));
    //@ ensures chars(p, 1, cons(value, nil));
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

predicate alloc_slice(char *p, int n) = chars(p, n, ?bytes);

#[requires(count > 0)]
#[ensures(alloc_slice(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
    //@ requires count > 0;
    //@ ensures alloc_slice(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(alloc_slice(start, count))]
#[ensures(alloc_slice(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    //@ requires alloc_slice(start, count);
    //@ ensures alloc_slice(start, count);
{
    let mut i = 0;
    /*@ 
    while(i < count)
        invariant 0 <= i && i <= count &*&
                  alloc_slice(start, count) &*&
                  byte_slice(start, i, ?prefix) &*& length(prefix) == i;
    @*/
    loop {
        if i == count { break; }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

#[requires(alloc_slice(start, count))]
#[ensures(alloc_slice(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    //@ requires alloc_slice(start, count);
    //@ ensures alloc_slice(start, count);
{
    let mut i = 0;
    /*@
    while(i < count)
        invariant 0 <= i && i <= count &*&
                  alloc_slice(start, count) &*&
                  byte_slice(start, count, ?bytes);
    @*/
    loop {
        if i == count { break; }
        let b = *start.add(i);
        write_byte(b);
        i += 1;
    }
}

fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}