use std::io::{stdin, stdout, Read, Write};

pred bytes(p: *mut u8, n: usize) =
    if n == 0 {
        emp
    } else {
        *(p as *mut u8) |-> ?v &*& bytes(p.add(1), n - 1)
    };

unsafe fn read_byte() -> u8
//@ requires emp;
//@ ensures emp;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ requires emp;
//@ ensures emp;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
//@ requires count > 0;
//@ ensures bytes(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ requires bytes(start, count);
//@ ensures bytes(start, count);
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
//@ requires bytes(text, count) &*& bytes(key, count);
//@ ensures bytes(text, count) &*& bytes(key, count);
{
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ requires bytes(start, count);
//@ ensures bytes(start, count);
{
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
}

fn main()
//@ requires emp;
//@ ensures emp;
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