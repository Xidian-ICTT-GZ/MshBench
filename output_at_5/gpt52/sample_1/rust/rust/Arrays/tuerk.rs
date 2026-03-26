use std::io::{Read, Write, stdin, stdout};

//@ pred bytes_(ptr: *mut u8, count: usize) = std::alloc::alloc_block(ptr as *mut u8, count);

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
//@ ens bytes_(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close bytes_(result, count);
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes_(start, count);
//@ ens bytes_(start, count);
{
    let mut i = 0;
    loop {
        //@ inv bytes_(start, count) &*& 0 <= i &*& i <= count;

        if i == count {
            break;
        }
        let b = read_byte();
        //@ open bytes_(start, count);
        *start.add(i) = b;
        //@ close bytes_(start, count);
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes_(start, count);
//@ ens bytes_(start, count);
{
    let mut i = 0;
    loop {
        //@ inv bytes_(start, count) &*& 0 <= i &*& i <= count;

        if i == count { break; }

        //@ open bytes_(start, count);
        write_byte(*start.add(i));
        //@ close bytes_(start, count);
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open bytes_(array, 100);
        std::alloc::dealloc(array, std::alloc::Layout::from_size_align(100, 1).unwrap());
    }
}