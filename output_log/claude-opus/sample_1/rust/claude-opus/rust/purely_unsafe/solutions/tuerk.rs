use std::io::{stdin, stdout, Read, Write};
use std::alloc::{alloc, handle_alloc_error, Layout};

predicate u8s(ptr: *mut u8, count: usize; vs: list<u8>) =
    count == 0 ?
        vs == nil
    :
        *ptr |-> ?v &*& u8s(ptr.offset(1), count - 1, ?tail) &*& vs == cons(v, tail);

unsafe fn read_byte() -> u8;
unsafe fn write_byte(value: u8);

#[ensures(result != null)]
#[ensures(u8s(result, count, take(count, repeat(0))))] 
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = Layout::from_size_align(count, 1).unwrap();
    let result = alloc(layout);
    if result.is_null() {
        handle_alloc_error(layout);
    }
    result
}

#[requires(u8s(start, count, _))]
#[ensures(u8s(start, count, ?vs))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    #[invariant(0 <= i && i <= count)] // i is the loop variable, tracked below
    #[invariant(u8s(start, i, take(i, vs)) &*& u8s(start.offset(i as isize), count - i, drop(i, vs)))]
{
    let mut i = 0;
    #[invariant(i <= count &*& u8s(start, i, take(i, ?vs_prefix)) &*& u8s(start.offset(i as isize), count - i, drop(i, ?vs_full)) &*& vs_prefix + drop(i, vs_full) == ?vs)]
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
    #[invariant(0 <= i && i <= count)]
    #[invariant(u8s(start, i, take(i, vs)) &*& u8s(start.offset(i as isize), count - i, drop(i, vs)))]
{
    let mut i = 0;
    #[invariant(i <= count &*& u8s(start, i, take(i, vs)) &*& u8s(start.offset(i as isize), count - i, drop(i, vs)))]
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