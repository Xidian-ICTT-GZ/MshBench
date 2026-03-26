use std::io::{Read, Write, stdin, stdout};

/*@ pred block(start: *mut u8, count: usize) = alloc_block(start, count); @*/

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
//@ ens block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req block(start, count);
//@ ens block(start, count);
{
    
    if count > 0 {
        //@ open block(start, count);
        let b = read_byte();
        *start = b;
        //@ close block(start.add(1), count - 1);
        read_bytes(start.add(1), count - 1);
        //@ close block(start, count);
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req block(start, count);
//@ ens block(start, count);
{
    if count > 0 {
        
        //@ open block(start, count);
        let b = *start;
        write_byte(b);
        //@ close block(start.add(1), count - 1);
        write_bytes(start.add(1), count - 1);
        //@ close block(start, count);
        
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