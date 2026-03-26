use std::io::{stdin, stdout, Read, Write};

#[predicate]
fn bytes(start: *mut u8, count: usize) -> bool {
    exists!<v: Seq<u8>> full_slice(start, count, v)
}

#[predicate]
fn full_slice(start: *mut u8, count: usize, v: Seq<u8>) -> bool {
    exists!<i: int> 0 <= i && i <= count &&
    forall!<j: int> 0 <= j && j < i ==> exists!<b: u8> *start.offset(j as isize) |-> b &&
    forall!<j: int> i <= j && j < count ==> *start.offset(j as isize) |-> _ &&
    v == Seq::new(i, |k: int| *start.offset(k as isize))
}

#[predicate]
fn slice(start: *mut u8, count: usize, i: usize, v: Seq<u8>) -> bool {
    i <= count &&
    forall!<j: int> 0 <= j && j < i as int ==> exists!<b: u8> *start.offset(j as isize) |-> b &&
    forall!<j: int> i as int <= j && j < count as int ==> *start.offset(j as isize) |-> _ &&
    v == Seq::new(i, |k: int| *start.offset(k as isize))
}

#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[ensures(result != std::ptr::null_mut())]
#[ensures(bytes(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(start != std::ptr::null_mut())]
#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(slice(start, count, i, _))]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();

        *start.add(i) = b;

        i += 1;
    }
}

#[requires(start != std::ptr::null_mut())]
#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(slice(start, count, i, _))]
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