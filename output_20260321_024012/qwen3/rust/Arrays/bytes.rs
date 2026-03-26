//@ pred bytes_slice(*mut u8 slice, usize len;) = true;

use std::io::{Read, Write, stdin, stdout};

//@ req true;
//@ ens true;
unsafe fn read_byte() -> u8

{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

//@ req true;
//@ ens true;
unsafe fn write_byte(value: u8)

{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

//@ req true;
//@ ens result != 0 as *mut u8;
unsafe fn alloc(count: usize) -> *mut u8

{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

//@ req bytes_slice(start, count);
//@ ens true;
unsafe fn read_bytes(start: *mut u8, count: usize)

{
    
    if count > 0 {
        //@ open bytes_slice(start, count);
        let b = read_byte();
        *start = b;
        //@ close bytes_slice(start.add(1), count - 1);
        read_bytes(start.add(1), count - 1);
        //@ close bytes_slice(start, count);
    } else {
        //@ close bytes_slice(start, 0);
    }
    
}

//@ req bytes_slice(start, count);
//@ ens true;
unsafe fn write_bytes(start: *mut u8, count: usize)

{
    if count > 0 {
        //@ open bytes_slice(start, count);
        let b = *start;
        write_byte(b);
        //@ close bytes_slice(start.add(1), count - 1);
        write_bytes(start.add(1), count - 1);
        //@ close bytes_slice(start, count);
    } else {
        //@ close bytes_slice(start, 0);
    }
}

fn main()

{
    unsafe {
        let array = alloc(100);
        //@ close bytes_slice(array, 100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        
    }
}