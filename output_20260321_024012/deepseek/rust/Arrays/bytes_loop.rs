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
//@ req count as int <= 0x7fffffff;
//@ ens [_]u8_block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req [?f]u8_block(start, count);
//@ ens [f]u8_block(start, count);
{
    //@ open u8_block(start, count);
    let mut i = 0;
    loop {
        //@ invariant 0 <= i && i <= count;
        //@ invariant [f]u8_block(start + i, count - i);
        if i == count { break; }
        let b = read_byte();
        //@ open u8_block(start + i, count - i);
        *start.add(i) = b;
        //@ close [f]u8_block(start + i, count - i);
        i += 1;
    }
    //@ close [f]u8_block(start, count);
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req [?f]u8_block(start, count);
//@ ens [f]u8_block(start, count);
{
    //@ open u8_block(start, count);
    let mut i = 0;
    loop {
        //@ invariant 0 <= i && i <= count;
        //@ invariant [f]u8_block(start + i, count - i);
        if i == count { break; }
        //@ open u8_block(start + i, count - i);
        let b = *start.add(i);
        //@ close [f]u8_block(start + i, count - i);
        write_byte(b);
        i += 1;
    }
    //@ close [f]u8_block(start, count);
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
        //@ leak u8_block(array, 100);
    }
}