use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

pred u8_at(p: *mut u8, v: u8) = *(p as *u8) |-> v;

pred u8_array(p: *mut u8, n: usize; vs: list<u8>) =
    n == 0 ?
        vs == nil
    :
        u8_at(p, ?v) &*& u8_array(p.add(1), n - 1; ?vs0) &*& vs == cons(v, vs0);

pred u8_array_ro(p: *const u8, n: usize; vs: list<u8>) =
    n == 0 ?
        vs == nil
    :
        *(p as *u8) |-> ?v &*& u8_array_ro(p.add(1), n - 1; ?vs0) &*& vs == cons(v, vs0);

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    //@ requires u8_array_ro(src, count; ?vs) &*& u8_array(dst, count; _);
    //@ ensures u8_array_ro(src, count; vs) &*& u8_array(dst, count; vs);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& u8_array_ro(src, count; vs) &*& u8_array(dst, i; take(i, vs)) &*& u8_array(dst.add(i), count - i; drop(i, vs));
        if i == count {
            break;
        }
        //@ open u8_array_ro(src.add(i), count - i; drop(i, vs));
        //@ open u8_array(dst.add(i), count - i; drop(i, vs));
        *dst.add(i) = *src.add(i);
        //@ close u8_array(dst.add(i), 1; take(1, drop(i, vs)));
        //@ close u8_array(dst.add(i), count - i; drop(i, vs));
        i += 1;
    }
    //@ assert u8_array(dst, count; vs);
}

fn main() {
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        //@ assert *(&raw const buffer1 as *const u8) |-> 10;
        //@ assert *((&raw const buffer1 as *const u8).add(1) as *u8) |-> 20;
        //@ assert *((&raw const buffer1 as *const u8).add(2) as *u8) |-> 30;
        //@ close u8_array_ro((&raw const buffer1 as *const u8), 3; cons(10, cons(20, cons(30, nil))));

        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close u8_array(buffer2, 3; _);

        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        //@ open u8_array(buffer2, 3; cons(10, cons(20, cons(30, nil))));
        //@ open u8_array(buffer2.add(1), 2; cons(20, cons(30, nil)));
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close u8_array(buffer2.add(1), 2; cons(20, cons(30, nil)));
        //@ close u8_array(buffer2, 3; cons(10, cons(20, cons(30, nil))));

        //@ open u8_array(buffer2, 3; cons(10, cons(20, cons(30, nil))));
        //@ open u8_array(buffer2.add(1), 2; cons(20, cons(30, nil)));
        //@ open u8_array(buffer2.add(2), 1; cons(30, nil));
        //@ open u8_array(buffer2.add(3), 0; nil);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
    }
}