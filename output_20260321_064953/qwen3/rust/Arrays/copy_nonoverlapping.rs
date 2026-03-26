//@ pred u8_slice(*u8 ptr, usize len;);

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req u8_slice(src, count) &*& u8_slice(dst, count);
//@ ens u8_slice(src, count) &*& u8_slice(dst, count);
{
    let mut i = 0;
    loop {
        //@ open u8_slice(src, count);
        //@ open u8_slice(dst, count);
        //@ close u8_slice(src, count);
        //@ close u8_slice(dst, count);
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close u8_slice(&raw const buffer1 as *const u8, 3);
        //@ close u8_slice(buffer2, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        
        //@ open u8_slice(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        
    }
}