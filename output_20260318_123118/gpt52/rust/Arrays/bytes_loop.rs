use std::io::{Read, Write, stdin, stdout};

pred bytes(ptr: *mut u8, count: usize; vs: list<u8>) =
    count == 0 ?
        vs == nil
    :
        ptr != 0 &*&
        ptr::u8(?v) &*&
        bytes(ptr.add(1), count - 1; ?vs0) &*&
        vs == cons(v, vs0);

unsafe fn read_byte() -> u8
//@ requires true;
//@ ensures true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ requires true;
//@ ensures true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
//@ requires count > 0;
//@ ensures bytes(result, count; ?vs) &*& length(vs) == count;
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ requires bytes(start, count; _);
//@ ensures bytes(start, count; ?vs) &*& length(vs) == count;
{
    
    let mut i = 0;
    //@ open bytes(start, count; _);
    //@ close bytes(start, count; ?vs0);
    loop {
        //@ invariant 0 <= i &*& i <= count &*& bytes(start, count; ?vs) &*& length(vs) == count;
        
        if i == count { break; }
        let b = read_byte();
        
        //@ open bytes(start.add(i), count - i; ?tail);
        *start.add(i) = b;
        //@ close bytes(start.add(i), count - i; cons(b, ?tail0));
        
        i += 1;
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ requires bytes(start, count; ?vs) &*& length(vs) == count;
//@ ensures bytes(start, count; vs);
{
    
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& bytes(start, count; vs) &*& length(vs) == count;
        
        if i == count { break; }
        
        //@ open bytes(start.add(i), count - i; ?tail);
        let b = *start.add(i);
        //@ close bytes(start.add(i), count - i; tail);
        
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