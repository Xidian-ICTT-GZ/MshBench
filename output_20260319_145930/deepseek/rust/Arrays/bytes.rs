use std::io::{Read, Write, stdin, stdout};

/*@
predicate_unsafe alloc_block_uchar_(pointer: *mut u8, count: usize) =
    count == 0 ? true : u8__own(pointer) &*& alloc_block_uchar_(pointer.offset(1), count - 1);
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
//@ ens alloc_block_uchar_(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req alloc_block_uchar_(start, count);
//@ ens alloc_block_uchar_(start, count);
{
    //@ open alloc_block_uchar_(start, count);
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
        //@ close alloc_block_uchar_(start, count);
    } else {
        //@ close alloc_block_uchar_(start, 0);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req alloc_block_uchar_(start, count);
//@ ens alloc_block_uchar_(start, count);
{
    //@ open alloc_block_uchar_(start, count);
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close alloc_block_uchar_(start, count);
    } else {
        //@ close alloc_block_uchar_(start, 0);
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
        //@ leak alloc_block_uchar_(array, 100);
    }
}