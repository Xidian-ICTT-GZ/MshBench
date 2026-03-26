use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
predicate alloc_block_u8(ptr: *mut u8, size: usize) = 
    size > 0 &*& malloc_block(ptr, size) &*& u8s(ptr, size);
@*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req [?f]u8s(src, count) &*& [?g]alloc_block_u8(dst, count);
//@ ens [f]u8s(src, count) &*& [g]alloc_block_u8(dst, count);
{
    let mut i = 0;
    //@ open [g]alloc_block_u8(dst, count);
    //@ open [g]u8s(dst, count);
    loop {
        //@ inv 0 <= i && i <= count &*& [f]u8s(src, count) &*& [g]u8s(dst, count) &*& [g]malloc_block(dst, count);
        if i == count { break; }
        //@ open [f]u8s(src, count);
        //@ open [g]u8s(dst, count);
        *dst.add(i) = *src.add(i);
        i += 1;
        //@ close [g]u8s(dst + (i-1), 1);
        //@ close [f]u8s(src + (i-1), 1);
        //@ recursive_call();
    }
    //@ close [g]u8s(dst, count);
    //@ close [g]alloc_block_u8(dst, count);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        //@ close u8s(&buffer1 as *const u8, 3);
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close alloc_block_u8(buffer2, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        //@ open alloc_block_u8(buffer2, 3);
        //@ open u8s(buffer2, 3);
        //@ open u8s(buffer2 + 1, _);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close u8s(buffer2 + 1, _);
        //@ close u8s(buffer2, 3);
        //@ close alloc_block_u8(buffer2, 3);
        
        //@ open alloc_block_u8(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        //@ open u8s(buffer2, 3);
        //@ open malloc_block(buffer2, 3);
        
    }
}