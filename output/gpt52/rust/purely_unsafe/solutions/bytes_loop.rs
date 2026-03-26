use std::io::{stdin, stdout, Read, Write};

pred u8s(p: *mut u8, count: usize; xs: list<u8>) =
    count == 0 ?
        xs == nil
    :
        p != 0 &*&
        *(p as *u8) |-> ?v &*&
        u8s(p.add(1), count - 1; ?vs) &*&
        xs == cons(v, vs);

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
    //@ requires count > 0;
    //@ ensures u8s(result, count; ?xs);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    //@ requires u8s(start, count; _);
    //@ ensures u8s(start, count; _);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& u8s(start, count; _);
        if i == count {
            break;
        }
        let b = read_byte();

        //@ open u8s(start, count; _);
        //@ close u8s(start, count; _);

        *start.add(i) = b;

        //@ open u8s(start, count; _);
        //@ close u8s(start, count; _);

        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    //@ requires u8s(start, count; _);
    //@ ensures u8s(start, count; _);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& u8s(start, count; _);
        if i == count {
            break;
        }

        //@ open u8s(start, count; _);
        //@ close u8s(start, count; _);

        let b = *start.add(i);

        write_byte(b);
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
        //@ leak u8s(array, 100; _);
    }
}