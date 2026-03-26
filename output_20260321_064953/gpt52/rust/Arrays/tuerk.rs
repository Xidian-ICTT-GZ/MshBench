use std::io::{Read, Write, stdin, stdout};

/*@

pred bytes_(ptr: *mut u8, count: usize) =
    count == 0 ?
        emp
    :
        std::alloc::alloc_block(ptr, count, 1) &*&
        std::alloc::alloc_block(ptr, count, 1);

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
//@ ens result != std::ptr::null_mut() &*& std::alloc::alloc_block(result, count, 1);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req std::alloc::alloc_block(start, count, 1);
//@ ens std::alloc::alloc_block(start, count, 1);
{
    let mut i = 0;
    loop {
        //@ inv std::alloc::alloc_block(start, count, 1) &*& 0 <= i &*& i <= count;
        if i == count {
            break;
        }
        let b = read_byte();
        //@ assert i < count;
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req std::alloc::alloc_block(start, count, 1);
//@ ens std::alloc::alloc_block(start, count, 1);
{
    let mut i = 0;
    loop {
        //@ inv std::alloc::alloc_block(start, count, 1) &*& 0 <= i &*& i <= count;
        if i == count { break; }
        //@ assert i < count;
        write_byte(*start.add(i));
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        //@ leak std::alloc::alloc_block(array, 100, 1);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}