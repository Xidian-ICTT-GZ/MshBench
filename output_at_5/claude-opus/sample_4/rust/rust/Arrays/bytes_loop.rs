use std::io::{Read, Write, stdin, stdout};

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
//@ requires true;
//@ ensures result != std::ptr::null_mut();
//@ ensures result as int != 0; // ensure non-null pointer
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ requires mutable_slice(start, count);
//@ ensures mutable_slice(start, count);
{
    let mut i = 0;
    while i < count
    //@ invariant 0 <= i as int <= count as int;
    //@ invariant mutable_slice(start, count);
    {
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ requires mutable_slice(start, count);
//@ ensures mutable_slice(start, count);
{
    let mut i = 0;
    while i < count
    //@ invariant 0 <= i as int <= count as int;
    //@ invariant mutable_slice(start, count);
    {
        let b = *start.add(i);
        write_byte(b);
        i += 1;
    }
}

//@ predicate mutable_slice(p: *mut u8, n: usize) =
//@     p != std::ptr::null_mut() &*& n > 0;

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