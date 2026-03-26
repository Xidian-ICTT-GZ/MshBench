use std::io::{stdin, stdout, Read, Write};

/*@

pred bytes(start: *mut u8, count: usize;) =
    if count == 0 {
        true
    } else {
        *start |-> _ &*& bytes(start.add(1), count - 1)
    };

lem bytes_split(start: *mut u8, count: usize, i: usize)
    req bytes(start, count) &*& i <= count;
    ens bytes(start, i) &*& bytes(start.add(i), count - i);
{
    if i == 0 {
    } else {
        open bytes(start, count);
        bytes_split(start.add(1), count - 1, i - 1);
        close bytes(start, i);
    }
}

lem bytes_join(start: *mut u8, count1: usize, count2: usize)
    req bytes(start, count1) &*& bytes(start.add(count1), count2);
    ens bytes(start, count1 + count2);
{
    if count1 == 0 {
        open bytes(start, 0);
    } else {
        open bytes(start, count1);
        bytes_join(start.add(1), count1 - 1, count2);
        close bytes(start, count1 + count2);
    }
}

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
//@ req count > 0;
//@ ens bytes(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop
    //@ inv bytes(start, count) &*& i <= count;
    {
        if i == count {
            break;
        }
        //@ bytes_split(start, count, i);
        //@ open bytes(start.add(i), count - i);
        let b = read_byte();
        *start.add(i) = b;
        //@ close bytes(start.add(i), count - i);
        //@ bytes_join(start, i, count - i);
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req bytes(start, count);
//@ ens bytes(start, count);
{
    let mut i = 0;
    loop
    //@ inv bytes(start, count) &*& i <= count;
    {
        if i == count {
            break;
        }
        //@ bytes_split(start, count, i);
        //@ open bytes(start.add(i), count - i);
        write_byte(*start.add(i));
        //@ close bytes(start.add(i), count - i);
        //@ bytes_join(start, i, count - i);
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