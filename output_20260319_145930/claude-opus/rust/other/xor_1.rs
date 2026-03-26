use std::io::{Read, Write, stdin, stdout};

//@ req true;
//@ ens true;
unsafe fn read_byte() -> u8
{
    //@ assume_correct
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

//@ req true;
//@ ens true;
unsafe fn write_byte(value: u8)
{
    //@ assume_correct
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

//@ req count >= 0;
//@ ens result != 0 as *mut u8 &*& alloc_block(result, count);
unsafe fn alloc(count: usize) -> *mut u8
{
    //@ assume_correct
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

//@ req count >= 0 &*& alloc_block(start, count);
//@ ens alloc_block(start, count);
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        //@ open alloc_block(start, count);
        let b = read_byte();
        *start = b;
        //@ close alloc_block(start.add(1), count - 1);
        read_bytes(start.add(1), count - 1);
        //@ open alloc_block(start.add(1), count - 1);
        //@ close alloc_block(start, count);
    }
}

//@ req count >= 0 &*& alloc_block(text, count) &*& alloc_block(key, count);
//@ ens alloc_block(text, count) &*& alloc_block(key, count);
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
{
    if count > 0 {
        //@ open alloc_block(text, count);
        //@ open alloc_block(key, count);
        let t = *text;
        let k = *key;
        *text = t ^ k;
        //@ close alloc_block(text.add(1), count - 1);
        //@ close alloc_block(key.add(1), count - 1);
        xor_bytes(text.add(1), key.add(1), count - 1);
        //@ open alloc_block(text.add(1), count - 1);
        //@ open alloc_block(key.add(1), count - 1);
        //@ close alloc_block(text, count);
        //@ close alloc_block(key, count);
    }
}

//@ req count >= 0 &*& alloc_block(start, count);
//@ ens alloc_block(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        //@ open alloc_block(start, count);
        let b = *start;
        write_byte(b);
        //@ close alloc_block(start.add(1), count - 1);
        write_bytes(start.add(1), count - 1);
        //@ open alloc_block(start.add(1), count - 1);
        //@ close alloc_block(start, count);
    }
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
    }
}