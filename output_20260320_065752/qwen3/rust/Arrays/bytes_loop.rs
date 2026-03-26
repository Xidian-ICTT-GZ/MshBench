use std::io::{Read, Write, stdin, stdout};

/*@ pred block(start: *mut u8, count: usize) = 
    alloc_block(start as *u8, count) &*&
    foreach(0, count, |i| u8_full_permission(start.add(i))); @*/

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
//@ req true;
//@ ens block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close block(result, count);
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req block(start, count);
//@ ens block(start, count);
{
    
    let mut i = 0;
    loop {
        //@ inv block(start, count) &*& 0 <= i &*& i <= count;
        
        if i == count { break; }
        let b = read_byte();
        
        *start.add(i) = b;
        
        i += 1;
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req block(start, count);
//@ ens block(start, count);
{
    
    let mut i = 0;
    loop {
        //@ inv block(start, count) &*& 0 <= i &*& i <= count;
        
        if i == count { break; }
        
        let b = *start.add(i);
        
        write_byte(b);
        i += 1;
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