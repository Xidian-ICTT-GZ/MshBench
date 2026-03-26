use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred bytes_(p: *mut u8, n: usize) =
    n == 0 ?
        true
    :
        *(p) |-> ?v &*& bytes_(p.add(1), n - 1);

@*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req bytes_(src as *mut u8, count) &*& bytes_(dst, count);
//@ ens bytes_(src as *mut u8, count) &*& bytes_(dst, count);
{
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& bytes_(src as *mut u8, count) &*& bytes_(dst, count);
        if i == count { break; }
        //@ open bytes_(src as *mut u8, count);
        //@ open bytes_(dst, count);
        *dst.add(i) = *src.add(i);
        //@ close bytes_(dst, count);
        //@ close bytes_(src as *mut u8, count);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            //@ assume_correct
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ assume_correct
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        //@ assume_correct
        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        //@ assume_correct
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
    }
}