use std::io::{Read, Write, stdin, stdout};

/*@

pred bytes_block(p: *mut u8, n: usize) =
    n == 0 ?
        true
    :
        std::alloc::alloc_block(p as *mut u8, n, 1) &*&
        std::alloc::alloc_block(p as *mut i8, n, 1);

@*/

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
//@ req 0 < count;
//@ ens bytes_block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close bytes_block(result, count);
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes_block(start, count);
//@ ens bytes_block(start, count);
{
    //@ open bytes_block(start, count);
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& bytes_block(start, count);
        if i == count { break; }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
    //@ close bytes_block(start, count);
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes_block(start, count);
//@ ens bytes_block(start, count);
{
    //@ open bytes_block(start, count);
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& bytes_block(start, count);
        if i == count { break; }
        let b = *start.add(i);
        write_byte(b);
        i += 1;
    }
    //@ close bytes_block(start, count);
}

fn main()
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}