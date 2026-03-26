use std::io::{Read, Write, stdin, stdout};

/*@ pred alloc_block_bytes(ptr: *mut u8, size: usize) = true; @*/

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
//@ ens alloc_block_bytes(result, count);
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    //@ close alloc_block_bytes(result, count);
    result
}

//@ req alloc_block_bytes(start, count);
//@ ens alloc_block_bytes(start, count);
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        let b = read_byte();
        //@ open alloc_block_bytes(start, count);
        *start = b;
        read_bytes(start.add(1), count - 1);
        //@ close alloc_block_bytes(start, count);
    }
    else {
        //@ close alloc_block_bytes(start, count);
    }
}

//@ req alloc_block_bytes(start, count);
//@ ens alloc_block_bytes(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        //@ open alloc_block_bytes(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close alloc_block_bytes(start, count);
    }
    else {
        //@ close alloc_block_bytes(start, count);
    }
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);

        
    }
}