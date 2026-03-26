use std::io::{Read, Write, stdin, stdout};

// verifast_options{}

//@ pred valid_slice(&u8* p, int count) = count == 0 || (p |-> ?v) &*& valid_slice(p + 1, count - 1);

unsafe fn read_byte() -> u8
//@ req true;
//@ ensures true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ req true;
//@ ensures true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
//@ req true;
//@ ensures result != std::ptr::null_mut();
//@ ensures valid_slice(result, count as int);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req valid_slice(start, count as int);
//@ ensures valid_slice(start, count as int);
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req valid_slice(start, count as int);
//@ ensures valid_slice(start, count as int);
{
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
}

fn main()
{
    unsafe {
        let array = alloc(100);
        //@ close valid_slice(array, 100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open valid_slice(array, 100);
    }
}