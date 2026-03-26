use std::io::{Read, Write, stdin, stdout};

pred bytes(ptr: *mut u8, count: usize;) =
    if count == 0 {
        true
    } else {
        ptr::read(ptr) |-> ?v &*& bytes(ptr.add(1), count - 1)
    };

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
//@ ensures bytes(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ requires bytes(start, count);
//@ ensures bytes(start, count);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& bytes(start, count);
        if i == count {
            break;
        }
        let b = read_byte();
        //@ open bytes(start, count);
        //@ assert ptr::read(start) |-> ?v0 &*& bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ requires bytes(start, count);
//@ ensures bytes(start, count);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& bytes(start, count);
        if i == count { break; }
        //@ open bytes(start, count);
        //@ assert ptr::read(start) |-> ?v0 &*& bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
        write_byte(*start.add(i));
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}