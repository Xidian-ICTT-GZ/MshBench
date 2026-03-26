use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred bytes(ptr: *mut u8, n: usize;) =
    n == 0 ?
        true
    :
        (*ptr |-> ?v) &*& bytes(ptr.add(1), n - 1);

pred bytes_ro(ptr: *const u8, n: usize;) =
    n == 0 ?
        true
    :
        (*ptr |-> ?v) &*& bytes_ro(ptr.add(1), n - 1);

@*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req bytes_ro(src, count) &*& bytes(dst, count);
//@ ens bytes_ro(src, count) &*& bytes(dst, count);
{
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& bytes_ro(src, count) &*& bytes(dst, count);

        if i == count { break; }
        //@ open bytes(dst, count);
        //@ open bytes_ro(src, count);
        *dst.add(i) = *src.add(i);
        //@ close bytes_ro(src, count);
        //@ close bytes(dst, count);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        //@ assert buffer1[0] == 10;
        //@ assert buffer1[1] == 20;
        //@ assert buffer1[2] == 30;

        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ assume(!buffer2.is_null());
        //@ close bytes(buffer2, 3);
        //@ close bytes_ro((&raw const buffer1 as *const u8), 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open bytes(buffer2, 3);
        //@ open bytes_ro((&raw const buffer1 as *const u8), 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        //@ close bytes(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        //@ open bytes(buffer2, 3);
    }
}