use std::io::{stdin, stdout, Read, Write};

/*@

pred bytes(start: *mut u8, count: usize;) =
    if count == 0 {
        true
    } else {
        *start |-> _ &*& bytes(start.add(1), count - 1)
    };

lem bytes_split(start: *mut u8, n: usize, m: usize)
    req bytes(start, n + m);
    ens bytes(start, n) &*& bytes(start.add(n), m);
{
    if n == 0 {
    } else {
        open bytes(start, n + m);
        bytes_split(start.add(1), n - 1, m);
        close bytes(start, n);
    }
}

lem bytes_join(start: *mut u8, n: usize, m: usize)
    req bytes(start, n) &*& bytes(start.add(n), m);
    ens bytes(start, n + m);
{
    if n == 0 {
        open bytes(start, 0);
    } else {
        open bytes(start, n);
        bytes_join(start.add(1), n - 1, m);
        close bytes(start, n + m);
    }
}

@*/

#[requires(count > 0)]
#[ensures(bytes(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        //@ open bytes(start, count);
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
    }
}

#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        //@ open bytes(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close bytes(start, count);
    }
}

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}