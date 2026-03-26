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
//@ ens result as usize != 0;
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req start as usize != 0;
//@ req count <= isize::MAX as usize;
//@ ens true;
{
    
    let mut i = 0;
    while i != count
    //@ inv start as usize != 0 &*& count <= isize::MAX as usize &*& 0 <= i &*& i <= count;
    {
        let b = read_byte();
        
        *start.add(i) = b;
        
        i += 1;
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req start as usize != 0;
//@ req count <= isize::MAX as usize;
//@ ens true;
{
    
    let mut i = 0;
    while i != count
    //@ inv start as usize != 0 &*& count <= isize::MAX as usize &*& 0 <= i &*& i <= count;
    {
        
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