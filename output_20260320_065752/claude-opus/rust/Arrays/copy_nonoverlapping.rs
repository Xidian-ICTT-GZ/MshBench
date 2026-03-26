use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred buffers(data: list<u8>, ptr: *mut u8, n: int) = 
    n == length(data) &*&
    malloc_block(ptr, n) &*&
    pointer_bytes(ptr, data);

@*/

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ req count >= 0 &*& pointer_bytes(src, ?dataSrc) &*& length(dataSrc) >= count &*& malloc_block(dst, count);
//@ ens pointer_bytes(dst, take(count, dataSrc));
{
    let mut i = 0;
    //@ open pointer_bytes(src, dataSrc);
    //@ open pointer_bytes(dst, ?prevDst);
    loop {
        //@ inv 0 <= i &*& i <= count &*&
        //@     pointer_bytes(src.add(i), drop(i, dataSrc)) &*&
        //@     pointer_bytes(dst.add(i), prevDst);
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        //@ i = i + 1;
        i += 1;
    }
    //@ close pointer_bytes(dst, take(count, dataSrc));
    //@ close pointer_bytes(src, dataSrc);
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
        //@ close pointer_bytes(&buffer1 as *const _ as *const u8, to_list([10u8,20,30]));
        //@ assume malloc_block(buffer2, 3);
        copy_nonoverlapping(&buffer1 as *const _ as *const u8, buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        //@ open pointer_bytes(buffer2, ?buf2data);
        dealloc(buffer2, layout);
    }
}