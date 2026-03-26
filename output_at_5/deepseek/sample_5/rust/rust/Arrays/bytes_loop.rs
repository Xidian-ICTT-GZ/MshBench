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
//@ ens [_]u8s(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req [?q]u8s(start, count);
//@ ens [q]u8s(start, count);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i && i <= count &*& [q]u8s(start + i, count - i);
        if i == count { break; }
        let b = read_byte();
        //@ open u8s(start + i, _);
        *start.add(i) = b;
        //@ close [q]u8s(start + i, 1);
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req [?q]u8s(start, count);
//@ ens [q]u8s(start, count);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i && i <= count &*& [q]u8s(start + i, count - i);
        if i == count { break; }
        //@ open u8s(start + i, _);
        let b = *start.add(i);
        //@ close [q]u8s(start + i, 1);
        write_byte(b);
        i += 1;
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ leak u8s(array, 100);
    }
}