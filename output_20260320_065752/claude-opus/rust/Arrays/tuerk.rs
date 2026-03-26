use std::io::{Read, Write, stdin, stdout};

/*@ 
predicate alloc_block_u8(void* p, usize n) = true; 
@*/

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
//@ ens result != core::ptr::null_mut();
//@ ensures alloc_block_u8(result, count);
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

//@ req alloc_block_u8(start, count);
//@ ens alloc_block_u8(start, count);
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    //@ while i < count
    //@ inv 0 <= i && i <= count &*& alloc_block_u8(start, count);
    {
        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

//@ req alloc_block_u8(start, count);
//@ ens alloc_block_u8(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    //@ while i < count
    //@ inv 0 <= i && i <= count &*& alloc_block_u8(start, count);
    {
        if i == count { break; }
        write_byte(*start.add(i));
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        //@ close alloc_block_u8(array, 100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open alloc_block_u8(array, 100);
    }
}