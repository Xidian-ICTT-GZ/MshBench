use std::io::{stdin, stdout, Read, Write};

predicate u8s(ptr: *mut u8, count: usize; vs: list<u8>) =
    count == 0 ?
        vs == nil
    :
        *ptr |-> ?v &*& u8s(ptr.offset(1), count - 1, ?tail) &*& vs == cons(v, tail);

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(u8s(result, count, ?vs))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    #[predicate]
    predicate alloc_bytes(p: *mut u8; n: usize) = 
        n > 0 &*& (p |-> _) &*& alloc_bytes(p.offset(1), n - 1) || n == 0 &*& true;
    // Use u8s predicate to describe ownership, assume zeroed memory or uninitialized:
    // To be conservative, after alloc, memory is uninitialized. 
    // VeriFast uses fragmentary ownership: reading uninit memory is unsafe, but since
    // read_bytes overwrites, it's allowed.
    result
}

#[requires(
    u8s(start, count, ?old_vs)
)]
#[ensures(
    u8s(start, count, ?new_vs)
)]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(
        i <= count &*& 
        u8s(start, i, take(i, ?vs1)) &*&
        u8s(start.offset(i as isize), count - i, ?vs2) &*&
        append(vs1, vs2) == old_vs
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

#[requires(
    u8s(start, count, ?vs)
)]
#[ensures(
    u8s(start, count, vs)
)]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(
        i <= count &*&
        u8s(start, count, ?vs_full) &*&
        take(i, vs_full) == take(i, vs) &*&
        drop(i, vs_full) == drop(i, vs)
    )]
    loop {
        if i == count {
            break;
        }

        write_byte(*start.add(i));
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