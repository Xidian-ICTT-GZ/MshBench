use std::io::{Read, Write, stdin, stdout};

/*@
predicate_ctor alloc_block(pointer: *mut u8, size: usize)() = 
    malloc_block(pointer, size) &*& pointer[..size] |-> _;
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
//@ req count > 0;
//@ ens alloc_block(result, count)();
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close alloc_block(result, count)();
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req alloc_block(start, count)();
//@ ens alloc_block(start, count)();
{
    //@ open alloc_block(start, count)();
    if count > 0 {
        let b = read_byte();
        *start = b;
        //@ close [1/2]malloc_block(start, 1);
        //@ close [1/2]start[..1] |-> _;
        read_bytes(start.add(1), count - 1);
        //@ open [1/2]malloc_block(start, 1);
        //@ open [1/2]start[..1] |-> _;
    }
    //@ close alloc_block(start, count)();
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req alloc_block(start, count)();
//@ ens alloc_block(start, count)();
{
    //@ open alloc_block(start, count)();
    if count > 0 {
        let b = *start;
        write_byte(b);
        //@ close [1/2]malloc_block(start, 1);
        //@ close [1/2]start[..1] |-> _;
        write_bytes(start.add(1), count - 1);
        //@ open [1/2]malloc_block(start, 1);
        //@ open [1/2]start[..1] |-> _;
    }
    //@ close alloc_block(start, count)();
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
        //@ open alloc_block(array, 100)();
        //@ leak malloc_block(array, 100) &*& array[..100] |-> _;
    }
}