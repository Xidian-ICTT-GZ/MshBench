use std::io::{Read, Write, stdin, stdout};

/*@ 
predicate bytes_slice(void* start, int count, list<u8> bytes) = 
    count == 0 ? start == null : 
    true &*& malloc_block(start, count);
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

//@ req true;
//@ ens result != std::ptr::null_mut::<u8>();
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

//@ req bytes_slice(start, count, ?bs);
//@ ens bytes_slice(start, count, ?bs2) &*& length(bs2) == count;
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    //@ open bytes_slice(start, count, ?bs);
    let mut i = 0;
    //@ let bs0 = bs;
    loop {
        //@ if i == 0 { } else { open bytes_slice(start, count, bs0); }
        //@ inv 0 <= i && i <= count &*& bytes_slice(start, count, ?bsl);
        if i == count { break; }
        let b = read_byte();
        //@ assert bytes_slice(start, count, bsl);
        *start.add(i) = b;
        //@ i += 1;
        i += 1;
    }
    //@ close bytes_slice(start, count, _);
}

//@ req bytes_slice(start, count, ?bs);
//@ ens bytes_slice(start, count, bs);
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    //@ open bytes_slice(start, count, ?bs);
    let mut i = 0;
    //@ let bs0 = bs;
    loop {
        //@ inv 0 <= i && i <= count &*& bytes_slice(start, count, bs0);
        if i == count { break; }
        let b = *start.add(i);
        write_byte(b);
        i += 1;
    }
    //@ close bytes_slice(start, count, bs0);
}

fn main()
{
    unsafe {
        let array = alloc(100);
        //@ close bytes_slice(array, 100, nil);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}