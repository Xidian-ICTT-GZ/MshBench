use std::io::{stdin, stdout, Read, Write};

predicate u8s(ptr: *mut u8, count: usize; vs: list<u8>) =
    count == 0 ?
        vs == nil
    :
        *ptr |-> ?v &*& u8s(ptr.offset(1), count - 1, ?tail) &*& vs == cons(v, tail);

unsafe fn read_byte() -> u8
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

predicate allocated_bytes(ptr: *mut u8, count: usize) = u8s(ptr, count, _);

#[ensures(allocated_bytes(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
    //@ requires count > 0;
    //@ ensures allocated_bytes(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(allocated_bytes(start, count))]
#[ensures(allocated_bytes(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    //@ requires allocated_bytes(start, count);
    //@ ensures allocated_bytes(start, count);
{
    let mut i = 0;
    //@ invariant 0 <= i && i <= count &*&
    //@           u8s(start, i, _) &*& u8s(start.offset(i as isize), count - i, _);
    while (i < count) {
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

#[requires(allocated_bytes(start, count))]
#[ensures(allocated_bytes(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    //@ requires allocated_bytes(start, count);
    //@ ensures allocated_bytes(start, count);
{
    let mut i = 0;
    //@ invariant 0 <= i && i <= count &*&
    //@           u8s(start, i, _) &*& u8s(start.offset(i as isize), count - i, _);
    while (i < count) {
        write_byte(*start.add(i));
        i += 1;
    }
}

fn main()
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}