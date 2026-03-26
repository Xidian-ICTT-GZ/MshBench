use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
predicate alloc_block_<u8>(start: *mut u8, len: usize) =
    len == 0 ?
        true
    :
        let next = start.offset(1);
        [start]u8 |-> ?val &*& alloc_block_<u8>(next, len - 1);
@*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req alloc_block_<u8>(src, count) &*& alloc_block_<u8>(dst, count);
//@ ens alloc_block_<u8>(src, count) &*& alloc_block_<u8>(dst, count);
{
    let mut i = 0;
    //@ close alloc_block_<u8>(src, count);
    //@ close alloc_block_<u8>(dst, count);
    loop {
        //@ inv 0 <= i && i <= count &*& alloc_block_<u8>(src.offset(i), count - i) &*& alloc_block_<u8>(dst.offset(i), count - i);
        if i == count { break; }
        //@ open alloc_block_<u8>(src.offset(i), count - i);
        //@ open alloc_block_<u8>(dst.offset(i), count - i);
        *dst.add(i) = *src.add(i);
        i += 1;
        //@ close alloc_block_<u8>(src.offset(i), count - i);
        //@ close alloc_block_<u8>(dst.offset(i), count - i);
    }
    //@ open alloc_block_<u8>(src.offset(count), 0);
    //@ open alloc_block_<u8>(dst.offset(count), 0);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close alloc_block_<u8>(buffer2, 3);
        //@ close alloc_block_<u8>(&raw const buffer1 as *const u8, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open alloc_block_<u8>(&raw const buffer1 as *const u8, 3);
        //@ open alloc_block_<u8>(buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        //@ open alloc_block_<u8>(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        
    }
}