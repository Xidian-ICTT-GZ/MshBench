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
//@ req count <= isize::MAX as usize;
//@ ens result as usize + count <= usize::MAX && alloc_block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req alloc_block(start, count);
//@ ens alloc_block(start, count);
{
    //@ open alloc_block(start, count);
    let mut i = 0;
    loop {
        //@ invariant 0 <= i && i <= count && alloc_block(start.offset(i as isize), count - i);
        if i == count { break; }
        let b = read_byte();
        //@ open alloc_block(start.offset(i as isize), count - i);
        //@ open u8__chars(start.offset(i as isize), _);
        *start.add(i) = b;
        //@ close u8__chars(start.offset(i as isize), _);
        //@ close alloc_block(start.offset(i as isize), count - i);
        i += 1;
    }
    //@ close alloc_block(start, count);
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req alloc_block(start, count);
//@ ens alloc_block(start, count);
{
    //@ open alloc_block(start, count);
    let mut i = 0;
    loop {
        //@ invariant 0 <= i && i <= count && alloc_block(start.offset(i as isize), count - i);
        if i == count { break; }
        //@ open alloc_block(start.offset(i as isize), count - i);
        //@ open u8__chars(start.offset(i as isize), _);
        let b = *start.add(i);
        //@ close u8__chars(start.offset(i as isize), _);
        //@ close alloc_block(start.offset(i as isize), count - i);
        write_byte(b);
        i += 1;
    }
    //@ close alloc_block(start, count);
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
        //@ leak alloc_block(array, 100);
    }
}