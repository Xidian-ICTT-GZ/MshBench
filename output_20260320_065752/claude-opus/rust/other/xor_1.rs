use std::io::{Read, Write, stdin, stdout};

/*@ pred alloc_block_u8(p: *mut u8, n: usize) = 
    (n == 0 &*& p == 0 as *mut u8) |
    (n > 0 &*& p != 0 as *mut u8 &*& pointer(p, _) &*& alloc_block_u8(p.offset(1), n - 1)); @*/

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

/*@ pred alloc_block(p: *mut u8, n: usize) = 
    (n == 0 &*& p == 0 as *mut u8) |
    (n > 0 &*& p != 0 as *mut u8 &*& pointer(p, _) &*& alloc_block(p.offset(1), n - 1)); @*/

//@ req true;
//@ ens result != 0 as *mut u8 &*& alloc_block(result, count);
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
unsafe fn read_bytes(mut start: *mut u8, count: usize)
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        
        //@ open alloc_block_u8(start, count);
        read_bytes(start.add(1), count - 1);
        //@ close alloc_block_u8(start, count);
    }
    else {
        
    }
}

//@ req alloc_block(text, count) &*& alloc_block(key, count);
//@ ens alloc_block(text, count) &*& alloc_block(key, count);
unsafe fn xor_bytes(mut text: *mut u8, mut key: *mut u8, count: usize)
{
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        //@ open alloc_block_u8(text, count);
        //@ open alloc_block_u8(key, count);
        xor_bytes(text.add(1), key.add(1), count - 1);
        //@ close alloc_block_u8(key, count);
        //@ close alloc_block_u8(text, count);
    }
}

//@ req alloc_block(start, count);
//@ ens alloc_block(start, count);
unsafe fn write_bytes(mut start: *mut u8, count: usize)
{
    if count > 0 {
        let b = *start;
        write_byte(b);
        //@ open alloc_block_u8(start, count);
        write_bytes(start.add(1), count - 1);
        //@ close alloc_block_u8(start, count);
    }
}

fn main()
{
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        //@ close alloc_block_u8(text, 10);
        //@ close alloc_block_u8(key, 10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
    }
}