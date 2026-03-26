use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

pred bytes(p: *mut u8, n: usize;) =
    if n == 0 {
        true
    } else {
        std::ptr::read::<u8>(p) |-> ?v &*& bytes(p.add(1), n - 1)
    };

pred bytes_ro(p: *const u8, n: usize;) =
    if n == 0 {
        true
    } else {
        std::ptr::read::<u8>(p) |-> ?v &*& bytes_ro(p.add(1), n - 1)
    };

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    //@ requires bytes_ro(src, count) &*& bytes(dst, count);
    //@ ensures bytes_ro(src, count) &*& bytes(dst, count);
{
    let mut i = 0;
    loop {
        //@ invariant 0 <= i &*& i <= count &*& bytes_ro(src, count) &*& bytes(dst, count);
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        //@ open std::ptr::read::<u8>(&raw const buffer1 as *const u8);
        //@ close bytes_ro(&raw const buffer1 as *const u8, 3);

        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ assume(buffer2 != std::ptr::null_mut());
        //@ close bytes(buffer2, 3);

        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        //@ open bytes(buffer2, 3);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close bytes(buffer2, 3);

        //@ open bytes(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        //@ open bytes_ro(&raw const buffer1 as *const u8, 3);
    }
}