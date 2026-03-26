use std::io::{stdin, stdout, Read, Write};

/*@
pred bytes(start: *mut u8, count: usize;) =
    if count == 0 {
        true
    } else {
        (*start) |-> _ &*& bytes(start.add(1), count - 1)
    };

lem bytes_split(start: *mut u8, i: usize, count: usize)
    req bytes(start, count) &*& i <= count;
    ens bytes(start, i) &*& bytes(start.add(i), count - i);
{
    if i == 0 {
    } else {
        open bytes(start, count);
        bytes_split(start.add(1), i - 1, count - 1);
        close bytes(start, i);
    }
}

lem bytes_join(start: *mut u8, i: usize, count: usize)
    req bytes(start, i) &*& bytes(start.add(i), count - i) &*& i <= count;
    ens bytes(start, count);
{
    if i == 0 {
        open bytes(start, 0);
    } else {
        open bytes(start, i);
        bytes_join(start.add(1), i - 1, count - 1);
        close bytes(start, count);
    }
}
@*/

#[requires(true)]
#[ensures(true)]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

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
    let mut i = 0;
    loop {
        //@ inv bytes(start, count) &*& i <= count;
        if i == count {
            break;
        }
        let b = read_byte();
        //@ bytes_split(start, i, count);
        //@ open bytes(start.add(i), count - i);
        *start.add(i) = b;
        //@ close bytes(start.add(i), count - i);
        //@ bytes_join(start, i, count);
        i += 1;
    }
}

#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        //@ inv bytes(start, count) &*& i <= count;
        if i == count {
            break;
        }
        //@ bytes_split(start, i, count);
        //@ open bytes(start.add(i), count - i);
        let b = *start.add(i);
        //@ close bytes(start.add(i), count - i);
        //@ bytes_join(start, i, count);
        write_byte(b);
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}