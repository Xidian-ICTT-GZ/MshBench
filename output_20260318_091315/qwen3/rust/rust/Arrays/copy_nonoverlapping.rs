use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate u8_slice(*u8 ptr, usize len) = 
    if len == 0 then emp else
        *ptr |-> _ &*& u8_slice(ptr.offset(1), len - 1);

lemma void u8_slice_split(*u8 ptr, usize i, usize j)
    requires u8_slice(ptr, i + j);
    ensures u8_slice(ptr, i) &*& u8_slice(ptr.offset(i), j);
{
    if i == 0 {
    } else {
        open u8_slice(ptr, i + j);
        u8_slice_split(ptr.offset(1), i - 1, j);
        close u8_slice(ptr, i);
    }
}

lemma void u8_slice_join(*u8 ptr, usize i, usize j)
    requires u8_slice(ptr, i) &*& u8_slice(ptr.offset(i), j);
    ensures u8_slice(ptr, i + j);
{
    if i == 0 {
    } else {
        open u8_slice(ptr, i);
        u8_slice_join(ptr.offset(1), i - 1, j);
        close u8_slice(ptr, i + j);
    }
}

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    requires u8_slice(src as *mut u8, count) &*& u8_slice(dst, count);
    ensures u8_slice(src as *mut u8, count) &*& u8_slice(dst, count);
{
    let mut i = 0;
    loop 
        invariant u8_slice(src as *mut u8, i) &*& u8_slice(src.add(i) as *mut u8, count - i) &*&
                  u8_slice(dst, i) &*& u8_slice(dst.add(i), count - i) &*&
                  0 <= i &*& i <= count;
    {
        if i == count { break; }
        open u8_slice(src.add(i) as *mut u8, count - i);
        open u8_slice(dst.add(i), count - i);
        *dst.add(i) = *src.add(i);
        close u8_slice(src.add(i) as *mut u8, count - i);
        close u8_slice(dst.add(i), count - i);
        i += 1;
    }
}

fn main()
    requires true;
    ensures true;
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        close u8_slice(buffer2, 3);
        close u8_slice(&buffer1[0] as *const u8 as *mut u8, 3);
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        open u8_slice(buffer2, 3);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        close u8_slice(buffer2, 3);
        
        open u8_slice(buffer2, 3);
        dealloc(buffer2, layout);
    }
}