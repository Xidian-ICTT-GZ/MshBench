use std::io::{Read, Write, stdin, stdout};

//@ predicate bytes_slice(void* p, int count, list<uint8_t> contents) = pointer(p, count) &*& slice(p, count, contents);

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
//@ ensures pointer(result, count);
//@ terminates;
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ requires count > 0 &*& pointer(start, count);
//@ ensures pointer(start, count);
//@ terminates;
{
    let mut i = 0;
    while i < count
    //@ invariant 0 <= i && i <= count &*& pointer(start, count);
    {
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ requires count > 0 &*& pointer(start, count);
//@ ensures pointer(start, count);
//@ terminates;
{
    let mut i = 0;
    while i < count
    //@ invariant 0 <= i && i <= count &*& pointer(start, count);
    {
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