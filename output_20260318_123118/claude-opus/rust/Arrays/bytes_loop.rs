use std::io::{Read, Write, stdin, stdout};

predicate byte_slice(u8* ptr, int count, list<u8> contents) =
    count > 0 ?
        ptr |-> ?b &*& byte_slice(ptr + 1, count - 1, ?rest) &*& b == head(contents) &*& rest == tail(contents)
    :
        true;

#[requires(true)]
#[ensures(result != 0)]
unsafe fn read_byte() -> u8
    //@ requires true;
    //@ ensures true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8)
    //@ requires true;
    //@ ensures true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

predicate alloc_block(u8* p, int count) = u8slice(p, count, _);

predicate u8slice(u8* p, int count, list<u8> vs) =
    count > 0 ?
        p |-> ?b &*& u8slice(p + 1, count - 1, ?rest) &*& b == head(vs) &*& rest == tail(vs)
    :
        true;

#[requires(count >= 0)]
#[ensures(alloc_block(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
    //@ requires count >= 0;
    //@ ensures alloc_block(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    
    result
}

#[requires(alloc_block(start, count))]
#[ensures(alloc_block(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    //@ requires alloc_block(start, count);
    //@ ensures alloc_block(start, count);
{
    let mut i = 0;
    //@ open alloc_block(start, count);
    while i < count
        //@ invariant 0 <= i && i <= count &*& u8slice(start, count, ?vs0) &*& length(vs0) == count;
    {
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
        //@ open u8slice(start, count, vs0);
        //@ close u8slice(start, count, update_nth(i - 1, b, vs0));
    }
    //@ close alloc_block(start, count);
}

#[requires(alloc_block(start, count))]
#[ensures(alloc_block(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    //@ requires alloc_block(start, count);
    //@ ensures alloc_block(start, count);
{
    let mut i = 0;
    //@ open alloc_block(start, count);
    while i < count
        //@ invariant 0 <= i && i <= count &*& u8slice(start, count, ?vs0) &*& length(vs0) == count;
    {
        let b = *start.add(i);
        write_byte(b);
        i += 1;
        //@ open u8slice(start, count, vs0);
        //@ close u8slice(start, count, vs0);
    }
    //@ close alloc_block(start, count);
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