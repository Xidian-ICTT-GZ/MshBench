use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

//@ pred slice_bytes(pointer: raw ptr<u8>, len: int) = pointer |-> ?data &*& length(data) == len &*& forall<i:int> 0 <= i && i < len ==> true;

/*@

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    //@ requires count as int >= 0 &*& slice_bytes(src, count as int) &*& slice_bytes(dst, count as int);
    //@ ensures slice_bytes(src, count as int) &*& slice_bytes(dst, count as int);
{
    let mut i = 0;
    loop {
        //@ if i as int == count as int { open slice_bytes(src, count as int); open slice_bytes(dst, count as int); close slice_bytes(src, count as int); close slice_bytes(dst, count as int); break; }
        
        
        if i == count { break; }
        //@ open slice_bytes(src, count as int);
        //@ open slice_bytes(dst, count as int);
        *dst.add(i) = *src.add(i);
        i += 1;
        //@ close slice_bytes(src, count as int);
        //@ close slice_bytes(dst, count as int);
    }
}

fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        //@ close slice_bytes(&raw const buffer1 as *const u8, 3);
        //@ close slice_bytes(buffer2, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open slice_bytes(buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        //@ open slice_bytes(buffer2, 3);
        dealloc(buffer2, layout);
    }
}