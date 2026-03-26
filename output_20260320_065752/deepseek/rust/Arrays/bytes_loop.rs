use std::io::{Read, Write, stdin, stdout};

/*@
predicate_ctor alloc_block(pointer: *mut u8, size: usize)() =
    pointer != 0
    &*& malloc_block(pointer, size)
    &*& pointer[..size] |-> ?bytes
    &*& bytes[..] |-> _;
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
//@ ens result != 0 &*& alloc_block(result, count)();
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
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& malloc_block(start, count) &*& start[..i] |-> ?prefix &*& start[i..count] |-> _;
        if i == count { break; }
        let b = read_byte();
        //@ assume_correct;
        *start.add(i) = b;
        i += 1;
    }
    //@ close alloc_block(start, count)();
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req alloc_block(start, count)();
//@ ens alloc_block(start, count)();
{
    //@ open alloc_block(start, count)();
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& malloc_block(start, count) &*& start[..i] |-> ?prefix &*& start[i..count] |-> ?suffix;
        if i == count { break; }
        let b = *start.add(i);
        write_byte(b);
        //@ assume_correct;
        i += 1;
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
        //@ dealloc(array);
    }
}