use std::io::{Read, Write, stdin, stdout};

/*@
predicate_ctor alloc_block(pointer: *mut u8, size: usize)() =
    pointer != 0 &*& malloc_block(pointer, size) &*&
    struct_from_slice(pointer, size, ?bytes) &*&
    bytes |-> ?slice &*& slice.len() == size &*&
    forall_(|i: usize| i < size ==> integer(&slice[i], ?val)) &*&
    true;
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
    if count > 0 {
        //@ open alloc_block(start, count)();
        let b = read_byte();
        *start = b;
        //@ assert integer(start, _);
        //@ close alloc_block(start.add(1), count - 1)();
        read_bytes(start.add(1), count - 1);
        //@ close alloc_block(start, count)();
    } else {
        //@ close alloc_block(start, 0)();
    }
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
//@ req alloc_block(text, count)() &*& alloc_block(key, count)();
//@ ens alloc_block(text, count)() &*& alloc_block(key, count)();
{
    if count > 0 {
        //@ open alloc_block(text, count)();
        //@ open alloc_block(key, count)();
        let t = *text;
        let k = *key;
        *text = t ^ k;
        //@ assert integer(text, _);
        //@ assert integer(key, _);
        //@ close alloc_block(text.add(1), count - 1)();
        //@ close alloc_block(key.add(1), count - 1)();
        xor_bytes(text.add(1), key.add(1), count - 1);
        //@ close alloc_block(text, count)();
        //@ close alloc_block(key, count)();
    } else {
        //@ close alloc_block(text, 0)();
        //@ close alloc_block(key, 0)();
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req alloc_block(start, count)();
//@ ens alloc_block(start, count)();
{
    if count > 0 {
        //@ open alloc_block(start, count)();
        let b = *start;
        write_byte(b);
        //@ assert integer(start, _);
        //@ close alloc_block(start.add(1), count - 1)();
        write_bytes(start.add(1), count - 1);
        //@ close alloc_block(start, count)();
    } else {
        //@ close alloc_block(start, 0)();
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
        //@ open alloc_block(text, 10)();
        //@ open alloc_block(key, 10)();
    }
}