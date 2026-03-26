use std::io::{Read, Write, stdin, stdout};

//@ pred valid_bytes(*mut u8 ptr, usize len) = foreach(i, 0, len, |i: int| sep(u8_full_permission(ptr.add(i as usize))));

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
//@ ens valid_bytes(result, count);

{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close valid_bytes(result, count);
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)

//@ req valid_bytes(start, count);
//@ ens valid_bytes(start, count);

{
    let mut i = 0;
    loop {

        //@ open valid_bytes(start, count);
        //@ close valid_bytes(start, count);

        if i == count {

            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;

    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)

//@ req valid_bytes(start, count);
//@ ens valid_bytes(start, count);

{
    let mut i = 0;
    loop {

        //@ open valid_bytes(start, count);
        //@ close valid_bytes(start, count);

        if i == count { break; }

        write_byte(*start.add(i));
        i += 1;

    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);

    }
}