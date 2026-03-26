use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred u8_block(ptr: *mut u8, len: usize) = if len == 0 { true } else { (*ptr |-> ?v) &*& u8_block(ptr.offset(1), len - 1) }; @*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req [?f]u8_block(src as *mut u8, count) &*& u8_block(dst, count);
//@ ens [f]u8_block(src as *mut u8, count) &*& u8_block(dst, count);
{
    let mut i = 0;
    //@ open u8_block(dst, count);
    //@ open u8_block(src as *mut u8, count);
    loop {
        //@ inv 0 <= i && i <= count &*& [f]u8_block((src as *mut u8).offset(i as isize), count - i) &*& u8_block(dst.offset(i as isize), count - i);
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
    //@ close u8_block(dst, count);
    //@ close u8_block(src as *mut u8, count);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        //@ close u8_block(buffer2, 3);
        //@ close u8_block(&buffer1[0] as *const u8 as *mut u8, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        
        //@ open u8_block(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        
    }
}