use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate u8_slice(*mut u8 ptr, usize len) = 
    if len == 0 then true else
        *ptr |-> _ &*& u8_slice(ptr.offset(1), len - 1);

lemma void u8_slice_split(*mut u8 ptr, usize i, usize len)
    requires u8_slice(ptr, len) &*& i <= len;
    ensures u8_slice(ptr, i) &*& u8_slice(ptr.offset(i), len - i);
{
    if i == 0 {
    } else {
        open u8_slice(ptr, len);
        u8_slice_split(ptr.offset(1), i - 1, len - 1);
        close u8_slice(ptr, i);
    }
}

lemma void u8_slice_join(*mut u8 ptr, usize i, usize len)
    requires u8_slice(ptr, i) &*& u8_slice(ptr.offset(i), len - i);
    ensures u8_slice(ptr, len);
{
    if i == 0 {
    } else {
        open u8_slice(ptr, i);
        u8_slice_join(ptr.offset(1), i - 1, len - 1);
        close u8_slice(ptr, len);
    }
}

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    requires [?f]u8_slice(src as *mut u8, count) &*& u8_slice(dst, count);
    ensures [f]u8_slice(src as *mut u8, count) &*& u8_slice(dst, count);
{
    let mut i = 0;
    loop 
        invariant [f]u8_slice(src as *mut u8, count) &*& u8_slice(dst, i) &*& u8_slice(dst.offset(i as isize), count - i) &*& i <= count;
    {
        if i == count { break; }
        open u8_slice(dst.offset(i as isize), count - i);
        *dst.add(i) = *src.add(i);
        close u8_slice(dst.offset(i as isize), count - i);
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
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        
        open u8_slice(buffer2, 3);
        dealloc(buffer2, layout);
        
    }
}