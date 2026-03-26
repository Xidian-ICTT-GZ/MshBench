use std::io::{Read, Write, stdin, stdout};

/*@

pred bytes_block(*u8 p, int n) =
    n <= 0 ?
        true
    :
        u8_at(p, _) &*& bytes_block(p + 1, n - 1);

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
//@ req true;
//@ ens bytes_block(result, count as int);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close bytes_block(result, count as int);
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes_block(start, count as int);
//@ ens bytes_block(start, count as int);
{
    
    if count > 0 {
        //@ open bytes_block(start, count as int);
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
        //@ close bytes_block(start, count as int);
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes_block(start, count as int);
//@ ens bytes_block(start, count as int);
{
    if count > 0 {
        
        //@ open bytes_block(start, count as int);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close bytes_block(start, count as int);
        
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