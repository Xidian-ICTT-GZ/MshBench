use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ requires *src |-> _ &*& *dst |-> _;
//@ ensures *dst |-> _;
{
    let mut i = 0;
    while i < count
    //@ invariant 0 <= i && i <= count &*& *src.add(i) |-> _ &*& *dst.add(i) |-> _;
    {
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
        //@ // Close permissions for buffer1
        //@ assert &buffer1 as *const _ as *const u8 |-> ?p1;
        //@ assert *(&buffer1 as *const _ as *const u8) |-> _; // permission to read first byte of buffer1
        //@ // Close permissions for buffer2
        //@ close *buffer2 |-> _;
        copy_nonoverlapping(&buffer1 as *const _ as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, layout);
    }
}