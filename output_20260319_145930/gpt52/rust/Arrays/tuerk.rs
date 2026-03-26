use std::io::{Read, Write, stdin, stdout};

/*@

pred bytes_(p: *mut u8, n: usize) =
    n == 0 ?
        true
    :
        std::alloc::alloc_block(p as *u8, n) &*&
        std::ptr::pointer_within_limits(p as *u8, n) &*&
        std::array::elements(p as *u8, n, _);

@*/

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

//@ req count <= isize::MAX as usize;
//@ ens bytes_(result, count);
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close bytes_(result, count);
    result
}

//@ req bytes_(start, count);
//@ ens bytes_(start, count);
unsafe fn read_bytes(start: *mut u8, count: usize)
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

//@ req bytes_(start, count);
//@ ens bytes_(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)
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

//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open bytes_(array, 100);
    }
}