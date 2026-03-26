use std::io::{Read, Write, stdin, stdout};

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

/*@

pred u8_array(ptr: *mut u8, count: usize;) =
    count == 0 ?
        true
    :
        ptr::is_not_null(ptr) &*&
        *ptr |-> _ &*&
        u8_array(ptr.add(1), count - 1);

@*/

unsafe fn alloc(count: usize) -> *mut u8
//@ req count > 0;
//@ ens u8_array(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req u8_array(start, count);
//@ ens u8_array(start, count);
{
    if count > 0 {
        //@ open u8_array(start, count);
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
        //@ close u8_array(start, count);
    }
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
//@ req u8_array(text, count) &*& u8_array(key, count);
//@ ens u8_array(text, count) &*& u8_array(key, count);
{
    if count > 0 {
        //@ open u8_array(text, count);
        //@ open u8_array(key, count);

        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);

        //@ close u8_array(key, count);
        //@ close u8_array(text, count);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req u8_array(start, count);
//@ ens u8_array(start, count);
{
    if count > 0 {
        //@ open u8_array(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close u8_array(start, count);
    }
}

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