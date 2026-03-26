use std::io::{Read, Write, stdin, stdout};

/*@

pred bytes_(ptr: *mut u8, count: usize) =
    count == 0 ?
        true
    :
        std::alloc::alloc_block(ptr as *mut u8, count, 1) &*&
        [_]std::alloc::alloc_block(ptr as *mut u8, count, 1);

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

//@ req count > 0;
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
    //@ open bytes_(start, count);
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& std::alloc::alloc_block(start as *mut u8, count, 1) &*& [_]std::alloc::alloc_block(start as *mut u8, count, 1);

        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
    //@ close bytes_(start, count);
}

//@ req bytes_(start, count);
//@ ens bytes_(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    //@ open bytes_(start, count);
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& std::alloc::alloc_block(start as *mut u8, count, 1) &*& [_]std::alloc::alloc_block(start as *mut u8, count, 1);

        if i == count { break; }

        write_byte(*start.add(i));
        i += 1;
    }
    //@ close bytes_(start, count);
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}