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
//@ ens result as int >= 0 &*& malloc_block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req malloc_block(start, count);
//@ ens malloc_block(start, count);
{
    let mut i = 0;
    loop {
        //@ inv 0 <= i as int &*& i as int <= count as int &*& malloc_block(start, count);
        //@ open malloc_block(start, count);
        //@ close malloc_block(start, count);
        if i == count {
            //@ close malloc_block(start, count);
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
        //@ close malloc_block(start, count);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req malloc_block(start, count);
//@ ens malloc_block(start, count);
{
    let mut i = 0;
    loop {
        //@ inv 0 <= i as int &*& i as int <= count as int &*& malloc_block(start, count);
        //@ open malloc_block(start, count);
        //@ close malloc_block(start, count);
        if i == count { 
            //@ close malloc_block(start, count);
            break; 
        }
        write_byte(*start.add(i));
        i += 1;
        //@ close malloc_block(start, count);
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open malloc_block(array, 100);
        //@ close malloc_block(array, 100);
    }
}