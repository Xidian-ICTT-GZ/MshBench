use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req [?f]src@.raw() &*& [?g]dst@.raw() &*& count <= src@.len() &*& count <= dst@.len();
//@ ens [f]src@.raw() &*& [g]dst@.raw();
{
    let mut i = 0;
    loop
    //@ inv [f]src@.raw() &*& [g]dst@.raw() &*& i <= count &*& forall(|k: usize| 0 <= k && k < i ==> *dst.offset(k as isize) == *src.offset(k as isize));
    {
        if i == count { break; }
        //@ open [f]src@.raw();
        //@ open [g]dst@.raw();
        *dst.add(i) = *src.add(i);
        //@ close [f]src@.raw();
        //@ close [g]dst@.raw();
        i += 1;
    }
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
        //@ close array<u8>(buffer2, 3, _);
        //@ close [1/2]buffer2@.raw();
        //@ close [1/2]buffer2@.raw();
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open [1/2]buffer2@.raw();
        //@ open array<u8>(buffer2, 3, _);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        //@ close array<u8>(buffer2, 3, _);
        //@ close [1/2]buffer2@.raw();
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        
    }
}