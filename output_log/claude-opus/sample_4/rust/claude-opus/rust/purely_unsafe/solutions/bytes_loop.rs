use std::io::{stdin, stdout, Read, Write};

predicate u8s(ptr: *mut u8, count: usize; vs: std::vec::Vec<u8>) =
    count == vs.len() &*&
    (count == 0 ? true : (*ptr |-> vs[0] &*& u8s(ptr.wrapping_add(1), count - 1, std::vec::Vec::from_slice(&vs[1..]))));

predicate u8s_uninit(ptr: *mut u8, count: usize) =
    count == 0 ?
        emp
    :
        *ptr |-> _ &*& u8s_uninit(ptr.wrapping_add(1), count - 1);

#[ensures(result |-> _ &*& u8s_uninit(&result, 1))]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(value |-> _)]
#[ensures(emp)]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(u8s_uninit(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(u8s_uninit(start, count))]
#[ensures(u8s(start, count, ?vs))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    requires count > 0
{
    let mut i = 0;
    #[invariant(0 <= i && i <= count &*&
        u8s(start, i, ?prefix) &*& u8s_uninit(start.wrapping_add(i), count - i) &
        prefix.len() == i
    )]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();

        *start.add(i) = b;
        i += 1;
    }
}

#[requires(u8s(start, count, ?vs))]
#[ensures(u8s(start, count, vs))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    requires count > 0
{
    let mut i = 0;
    #[invariant(0 <= i && i <= count &*& u8s(start, count, vs))]
    loop {
        if i == count {
            break;
        }

        let b = *start.add(i);

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