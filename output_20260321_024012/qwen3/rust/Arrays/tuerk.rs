//@ pred bytes_slice(*mut u8 ptr, usize len;);

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
//@ ens bytes_slice(start, count);
unsafe fn read_bytes(start: *mut u8, count: usize)

{
    let mut i = 0;
    loop {
        

        
        if i == count {
            
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
        
        
    }
}

//@ req bytes_slice(start, count);
//@ ens bytes_slice(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)

{
    let mut i = 0;
    loop {
        

        if i == count { break; }
        
        write_byte(*start.add(i));
        i += 1;
        
        
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        //@ close bytes_slice(array, 100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open bytes_slice(array, 100);
        
    }
}