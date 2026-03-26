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

/*@
pred bytes(ptr: *mut u8, count: usize) =
    if count == 0 {
        true
    } else {
        std::alloc::alloc_block(ptr as *u8, 1) &*& bytes(ptr.add(1), count - 1)
    };
@*/

unsafe fn alloc(count: usize) -> *mut u8
//@ req count > 0;
//@ ens bytes(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    
    if count > 0 {
        //@ open bytes(start, count);
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    if count > 0 {
        
        //@ open bytes(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
        
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