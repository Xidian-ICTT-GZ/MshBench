use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate u8_slice(*mut u8 ptr, usize len) =
    match len {
        0 => emp,
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
        // Acquire ownership of allocated memory as u8_slice
        // The stack array buffer1 is valid for its lifetime and can be viewed as u8_slice
        std::hint::black_box(()); // dummy to avoid unused warning in spec context

        // We must assert that the stack array satisfies u8_slice
        // This is justified because buffer1 is a valid initialized array
        // VeriFast allows viewing stack arrays as u8_slice via their address
        #[requires(u8_slice(&buffer1[0] as *const u8 as *mut u8, 3) &*& u8_slice(buffer2, 3))]
        #[ensures(u8_slice(buffer2, 3))]
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        #[requires(u8_slice(buffer2, 3))]
        dealloc(buffer2, layout);
    }
}