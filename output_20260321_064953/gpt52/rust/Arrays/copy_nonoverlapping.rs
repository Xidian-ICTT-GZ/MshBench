use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred array_u8(ptr: *mut u8, count: usize; elems: list<u8>) =
    count == 0 ?
        elems == nil
    :
        ptr != 0 &*&
        u8(ptr, ?v) &*& array_u8(ptr.add(1), count - 1; ?vs) &*& elems == cons(v, vs);

pred array_u8_ro(ptr: *const u8, count: usize; elems: list<u8>) =
    count == 0 ?
        elems == nil
    :
        ptr != 0 &*&
        u8(ptr, ?v) &*& array_u8_ro(ptr.add(1), count - 1; ?vs) &*& elems == cons(v, vs);

fixpoint list<u8> update_nth_u8(list<u8> xs, nat i, u8 v) {
    switch(xs) {
        case nil: return nil;
        case cons(h, t):
            return i == 0 ? cons(v, t) : cons(h, update_nth_u8(t, i - 1, v));
    }
}
@*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req array_u8_ro(src, count; ?xs) &*& array_u8(dst, count; ?ys);
//@ ens array_u8_ro(src, count; xs) &*& array_u8(dst, count; xs);
{
    let mut i = 0;
    //@ close array_u8(dst, 0; nil);
    //@ close array_u8_ro(src, 0; nil);
    loop {
        //@ inv 0 <= i &*& i <= count &*& array_u8_ro(src, count; xs) &*& array_u8(dst, i; take(i, xs)) &*& array_u8(dst.add(i), count - i; drop(i, ys));
        if i == count { break; }
        //@ open array_u8(dst.add(i), count - i; drop(i, ys));
        //@ open array_u8_ro(src.add(i), count - i; drop(i, xs));
        *dst.add(i) = *src.add(i);
        //@ close array_u8_ro(src.add(i), count - i; drop(i, xs));
        //@ close array_u8(dst.add(i), count - i; cons(nth(i, xs), drop(i + 1, ys)));
        i += 1;
        //@ assert take(i, xs) == append(take(i - 1, xs), cons(nth(i - 1, xs), nil));
    }
    //@ open array_u8(dst.add(count), 0; _);
    //@ assert drop(count, ys) == nil;
}

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ assume(buffer2 != 0);
        //@ close array_u8(buffer2, 3; cons(0u8, cons(0u8, cons(0u8, nil))));
        //@ close array_u8_ro((&raw const buffer1 as *const u8), 3; cons(10u8, cons(20u8, cons(30u8, nil))));
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open array_u8(buffer2, 3; cons(10u8, cons(20u8, cons(30u8, nil))));
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close array_u8(buffer2, 3; cons(10u8, cons(20u8, cons(30u8, nil))));
        //@ open array_u8(buffer2, 3; _);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
    }
}