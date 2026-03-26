use std::io::{stdin, stdout, Read, Write};

/*@

pred bytes(ptr: *mut u8, count: usize;) =
    if count == 0 {
        true
    } else {
        *ptr |-> _ &*& bytes(ptr.add(1), count - 1)
    };

@*/

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
//@ ens bytes(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ assume(bytes(result, count));
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop {
        //@ inv bytes(start, count) &*& i <= count;
        if i == count {
            break;
        }
        let b = read_byte();
        //@ open bytes(start.add(i), count - i);
        *start.add(i) = b;
        //@ close bytes(start.add(i), count - i);
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop {
        //@ inv bytes(start, count) &*& i <= count;
        if i == count {
            break;
        }
        //@ open bytes(start.add(i), count - i);
        write_byte(*start.add(i));
        //@ close bytes(start.add(i), count - i);
        i += 1;
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}