use std::io::{Read, Write, stdin, stdout};

/*@

pred bytes_(ptr: *mut u8, count: usize) =
    count == 0 ?
        true
    :
        std::ptr::read(ptr) |-> ?v &*& bytes_(ptr.add(1), count - 1);

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
//@ req count > 0;
//@ ens result != std::ptr::null_mut() &*& std::alloc::alloc_block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req std::alloc::alloc_block(start, count);
//@ ens std::alloc::alloc_block(start, count);
{
    if count > 0 {
        let b = read_byte();
        //@ assume_correct
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req std::alloc::alloc_block(start, count);
//@ ens std::alloc::alloc_block(start, count);
{
    if count > 0 {
        //@ assume_correct
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
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