use std::io::{Read, Write, stdin, stdout};

//@ pred valid_ptr(*mut u8, usize);

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

//@ req count <= usize::MAX;
//@ ens valid_ptr(result, count);

{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close valid_ptr(result, count);
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)

//@ req valid_ptr(start, count);
//@ ens valid_ptr(start, count);

{
    
    if count > 0 {
        //@ open valid_ptr(start, count);
        let b = read_byte();
        *start = b;
        //@ close valid_ptr(start.add(1), count - 1);
        read_bytes(start.add(1), count - 1);
        //@ close valid_ptr(start, count);
    } else {
        //@ close valid_ptr(start, 0);
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)

//@ req valid_ptr(start, count);
//@ ens valid_ptr(start, count);

{
    if count > 0 {
        
        //@ open valid_ptr(start, count);
        let b = *start;
        write_byte(b);
        //@ close valid_ptr(start.add(1), count - 1);
        write_bytes(start.add(1), count - 1);
        //@ close valid_ptr(start, count);
    } else {
        //@ close valid_ptr(start, 0);
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
        
    }
}