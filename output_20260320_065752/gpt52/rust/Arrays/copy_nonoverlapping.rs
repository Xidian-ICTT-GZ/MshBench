use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred bytes_(ptr: *mut u8, count: usize) =
    count == 0 ?
        true
    :
        std::ptr::read(ptr) |-> ?v &*& bytes_(ptr.add(1), count - 1);

pred bytes(ptr: *mut u8, count: usize) =
    std::alloc::alloc_block(ptr, Layout::from_size_align_unchecked(count, 1)) &*& bytes_(ptr, count);

@*/

//@ req src != 0 as *const u8 &*& dst != 0 as *mut u8 &*& bytes(dst, count) &*& bytes_((src as *mut u8), count);
//@ ens bytes(dst, count) &*& bytes_((src as *mut u8), count);
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)

{
    let mut i = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& bytes(dst, count) &*& bytes_((src as *mut u8), count);
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()

{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ assume(buffer2 != std::ptr::null_mut());
        //@ close bytes(buffer2, 3);
        //@ close bytes_((&raw const buffer1 as *const u8) as *mut u8, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        
        //@ open bytes(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        
    }
}