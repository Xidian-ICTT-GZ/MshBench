use std::io::{Read, Write, stdin, stdout};

//@ assume_correct
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

//@ assume_correct
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

//@ req count >= 0;
//@ ens result != 0 &*& alloc_block(result, count);
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

//@ req alloc_block(start, count);
//@ ens alloc_block(start, count);
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    loop {
        //@ inv alloc_block(start, count) &*& i >= 0 &*& i <= count;
        
        if i == count {
            break;
        }
        let b = read_byte();
        //@ open alloc_block(start, count);
        *start.add(i) = b;
        //@ close alloc_block(start, count);
        i += 1;
    }
}

//@ req alloc_block(start, count);
//@ ens alloc_block(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    loop {
        //@ inv alloc_block(start, count) &*& i >= 0 &*& i <= count;

        if i == count { break; }
        
        //@ open alloc_block(start, count);
        write_byte(*start.add(i));
        //@ close alloc_block(start, count);
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}