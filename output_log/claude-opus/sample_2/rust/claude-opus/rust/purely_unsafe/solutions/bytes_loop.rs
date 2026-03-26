use std::io::{stdin, stdout, Read, Write};
use std::alloc::{alloc, handle_alloc_error, Layout};

predicate u8s(ptr: *mut u8, count: usize; vs: std::vec::Vec<u8>) =
    count == vs.len() &*&
    count == 0 ?
        emp
    :
        *ptr |-> vs[0] &*& u8s(ptr.wrapping_add(1), count - 1, vs[1..].to_vec());

predicate u8s_uninit(ptr: *mut u8, count: usize) =
    count == 0 ?
        emp
    :
        *ptr |-> _ &*& u8s_uninit(ptr.wrapping_add(1), count - 1);

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
#[ensures(u8s_uninit(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = Layout::from_size_align(count, 1).unwrap();
    let result = alloc(layout);
    if result.is_null() {
        handle_alloc_error(layout);
    }
    result
}

#[requires(u8s_uninit(start, count))]
#[ensures(exists |vs: std::vec::Vec<u8>| u8s(start, count, vs))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count &*&
        exists |fst: std::vec::Vec<u8>, snd: std::vec::Vec<u8>|
            fst.len() == i &*&
            snd.len() == count - i &*&
            u8s(start, i, fst) &*&
            u8s_uninit(start.wrapping_add(i), count - i) &*&
            fold(std::vec::Vec::<u8>::append(fst, snd), |x| x.len() == count))]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();

        *start.add(i) = b;

        i += 1;
    }
}

#[requires(exists |vs: std::vec::Vec<u8>| u8s(start, count, vs))]
#[ensures(exists |vs: std::vec::Vec<u8>| u8s(start, count, vs))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count &*&
        exists |vs: std::vec::Vec<u8>|
            u8s(start, count, vs))]
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