use std::io::{Read, Write, stdin, stdout};

//@ pred slice(p: pointer<u8>, n: int) = chars(p, n, _);

unsafe fn read_byte() -> u8
//@ requires true;
//@ ensures true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ requires true;
//@ ensures true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
//@ requires true;
//@ ensures result != std::ptr::null_mut() ==> slice(result, count as int);
//@ ensures true;
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ requires slice(start, count as int);
//@ ensures slice(start, count as int);
{
    let mut i = 0;
    loop {
        if i == count { break; }
        //@ open slice(start + i as int, 1);
        let b = read_byte();
        *start.add(i) = b;
        //@ close slice(start + i as int, 1);
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ requires slice(start, count as int);
//@ ensures slice(start, count as int);
{
    let mut i = 0;
    loop {
        if i == count { break; }
        //@ open slice(start + i as int, 1);
        let b = *start.add(i);
        write_byte(b);
        //@ close slice(start + i as int, 1);
        i += 1;
    }
}

fn main()
//@ requires true;
//@ ensures true;
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}