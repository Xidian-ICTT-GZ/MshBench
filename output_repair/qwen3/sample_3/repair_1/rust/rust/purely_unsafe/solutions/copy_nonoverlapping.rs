use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate u8_slice(*mut u8 ptr, usize len) =
    if len == 0 then
        true
    else
        *ptr |-> _ &*& u8_slice(ptr.offset(1), len - 1);

predicate u8_const_slice(*const u8 ptr, usize len) =
    if len == 0 then
        true
    else
        *ptr |-> _ &*& u8_const_slice(ptr.offset(1), len - 1);

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    #[requires(u8_const_slice(src, count) &*& u8_slice(dst, count))]
    #[ensures(u8_const_slice(src, count) &*& u8_slice(dst, count))]
    let mut i = 0;
    #[invariant(i <= count &*& u8_const_slice(src, count) &*& u8_slice(dst, i) &*& u8_slice(dst.add(i), count - i))]
    loop {
        if i == count {
            break;
        }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main() {
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        #[requires(u8_const_slice(&raw const buffer1 as *const u8, 3) &*& buffer2 != std::ptr::null_mut())]
        #[ensures(u8_const_slice(&raw const buffer1 as *const u8, 3) &*& u8_slice(buffer2, 3))]
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        #[requires(u8_slice(buffer2, 3))]
        dealloc(buffer2, layout);
    }
}