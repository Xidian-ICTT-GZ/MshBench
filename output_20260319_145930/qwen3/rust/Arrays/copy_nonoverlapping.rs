use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred u8_block(ptr: *mut u8, len: usize) = if len == 0 then true else
    alloc_block_(ptr, len) &*& forall(i: usize; i < len ==> u8_full_perm(ptr.add(i))); @*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req u8_block(dst, count) &*& [?f]u8_block(src as *mut u8, count);
//@ ens u8_block(dst, count) &*& [f]u8_block(src as *mut u8, count);
{
    let mut i = 0;
    //@ open u8_block(dst, count);
    //@ open u8_block(src as *mut u8, count);
    loop {
        //@ inv 0 <= i &*& i <= count &*&
        //@       alloc_block_(dst, count) &*&
        //@       forall(j: usize; j < i ==> u8_full_perm(dst.add(j))) &*&
        //@       [f]alloc_block_(src as *mut u8, count) &*&
        //@       [f]forall(j: usize; j < count ==> u8_full_perm((src as *mut u8).add(j)));
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
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close u8_block(buffer2, 3);
        //@ close u8_block(&raw mut buffer1 as *mut u8, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        
        //@ open u8_block(buffer2, 3);
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        
    }
}