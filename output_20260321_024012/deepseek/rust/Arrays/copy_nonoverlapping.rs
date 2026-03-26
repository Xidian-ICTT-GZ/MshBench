use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req count <= isize::MAX as usize;
//@ ens true;
{
    let mut i = 0;
    //@ close array<u8>(_, _, _);
    loop {
        //@ inv 0 <= i && i <= count;
        //@ inv array<u8>(src, count, _);
        //@ inv array<u8>(dst, count, _);
        if i == count { break; }
        //@ open array<u8>(src, count, _);
        //@ open array<u8>(dst, count, _);
        *dst.add(i) = *src.add(i);
        i += 1;
        //@ close array<u8>(src, count, _);
        //@ close array<u8>(dst, count, _);
    }
    //@ open array<u8>(_, _, _);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        //@ close array<u8>(buffer1.as_ptr(), 3, _);
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close array<u8>(buffer2, 3, _);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open array<u8>(buffer2, 3, _);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close array<u8>(buffer2, 3, _);
        //@ open array<u8>(buffer2, 3, _);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        //@ leak array<u8>(buffer1.as_ptr(), 3, _);
    }
}