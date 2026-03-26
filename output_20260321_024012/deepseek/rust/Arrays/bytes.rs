use std::io::{Read, Write, stdin, stdout};

unsafe fn read_byte() -> u8
//@ req true;
//@ ens true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ req true;
//@ ens true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
//@ req count as int >= 0;
//@ ens result as int >= 0;
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req start as int >= 0 &*& count as int >= 0;
//@ ens true;
{
    //@ open u8s_(start, count, _);
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
    //@ close u8s_(start, count, _);
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req u8s_(start, count, _);
//@ ens u8s_(start, count, _);
{
    //@ open u8s_(start, count, _);
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
    //@ close u8s_(start, count, _);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let array = alloc(100);
        //@ close u8s_(array, 100, _);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open u8s_(array, 100, _);
    }
}