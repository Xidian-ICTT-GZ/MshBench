use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate u8_slice(*mut u8 ptr, usize len) = 
    match len {
        0 => true,
        _ => *ptr |-> _ &*& u8_slice(ptr.offset(1), len - 1)
    };

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    #[requires(u8_slice(src as *mut u8, count) &*& u8_slice(dst, count))]
    #[ensures(u8_slice(src as *mut u8, count) &*& u8_slice(dst, count))]
    let mut i = 0;
    #[invariant(i <= count &*& u8_slice(src as *mut u8, count) &*& u8_slice(dst, count))]
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
        // Initialize allocated memory to satisfy u8_slice predicate
        std::ptr::write_bytes(buffer2, 0u8, 3);
        // Now we own u8_slice(buffer2, 3)
        copy_nonoverlapping(&buffer1[0] as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, layout);
    }
}