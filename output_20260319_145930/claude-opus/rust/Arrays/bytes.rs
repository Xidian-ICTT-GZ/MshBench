use std::io::{Read, Write, stdin, stdout};

//@ assume_correct
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

//@ assume_correct
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

/*@

pred bytes(start: *mut u8, count: usize;) =
    if count == 0 {
        true
    } else {
        *start |-> _ &*& bytes(start.add(1), count - 1)
    };

@*/

//@ req count > 0 &*& std::alloc::Layout::from_size_align(count, 1) == Ok(?layout);
//@ ens bytes(result, count);
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ assume(bytes(result, count));
    result
}

//@ req bytes(start, count);
//@ ens bytes(start, count);
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    //@ open bytes(start, count);
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
    //@ close bytes(start, count);
}

//@ req bytes(start, count);
//@ ens bytes(start, count);
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    //@ open bytes(start, count);
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
    }
    //@ close bytes(start, count);
}

fn main()
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ leak bytes(array, 100);
    }
}