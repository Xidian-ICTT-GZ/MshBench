//@ req true;
//@ ens true;
use std::io::{Read, Write, stdin, stdout};

/*@ pred u8_block(ptr: *mut u8, len: usize) = if len == 0 then true else
    alloc_block_u8(ptr, len) &*& [_]u8_full_perm::<u8>(ptr); @*/

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
//@ ens u8_block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close u8_block(result, count);
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req u8_block(start, count);
//@ ens u8_block(start, count);
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        //@ open u8_block(start, count);
        read_bytes(start.add(1), count - 1);
        //@ close u8_block(start, count);
    }
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
//@ req u8_block(text, count) &*& u8_block(key, count);
//@ ens u8_block(text, count) &*& u8_block(key, count);
{
    if count > 0 {
        //@ open u8_block(text, count);
        //@ open u8_block(key, count);
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
        //@ close u8_block(text, count);
        //@ close u8_block(key, count);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req u8_block(start, count);
//@ ens u8_block(start, count);
{
    if count > 0 {
        //@ open u8_block(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close u8_block(start, count);
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
    }
}