use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

//@ predicate raw_ptr_bytes(void *p, int n) = true;

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ requires raw_ptr_bytes(src as *void, count) &*& raw_ptr_bytes(dst as *void, count);
//@ ensures raw_ptr_bytes(src as *void, count) &*& raw_ptr_bytes(dst as *void, count);
{
    let mut i = 0;
    loop {
        //@ if i == (int)count { break; }
        //@ open raw_ptr_bytes(src as *void, count);
        //@ open raw_ptr_bytes(dst as *void, count);
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        //@ close raw_ptr_bytes(&buffer1 as *const _ as *void, 3);
        //@ assume(raw_ptr_bytes(&buffer1 as *const _ as *void, 3));
        //@ close raw_ptr_bytes(buffer2 as *void, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        dealloc(buffer2, layout);
    }
}