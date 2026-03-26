use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req [?q]src@.len() >= count &*& [?r]dst@.len() >= count &*& count <= 0xffffffff;
//@ ens [q]src@.len() >= count &*& [r]dst@.len() >= count &*& mut_slice(dst, count, ?vals) &*& vals == src[..count];
{
    let mut i = 0;
    //@ close [q]slice::<u8>(src, 0, _);
    //@ close [r]mut_slice::<u8>(dst, 0, _);
    loop
    //@ inv 0 <= i && i <= count &*& [q]slice(src + i, count - i, _) &*& [r]mut_slice(dst + i, count - i, ?vals2) &*& vals2 == src[..count][i..];
    {
        if i == count { break; }
        //@ open [q]slice(src + i, _, _);
        //@ open [r]mut_slice(dst + i, _, _);
        *dst.add(i) = *src.add(i);
        i += 1;
        //@ close [q]slice(src + i, count - i, _);
        //@ close [r]mut_slice(dst + i, count - i, _);
    }
    //@ open [q]slice(src + count, 0, _);
    //@ open [r]mut_slice(dst + count, 0, _);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        //@ close array_u8(buffer1.as_ptr(), 3, _);
        //@ close slice(buffer1.as_ptr(), 3, _);
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close mut_slice(buffer2, 3, _);
        copy_nonoverlapping(buffer1.as_ptr(), buffer2, 3);
        //@ open mut_slice(buffer2, 3, _);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ open mut_slice(buffer2, 3, _);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        //@ leak slice(buffer1.as_ptr(), 3, _);
    }
}