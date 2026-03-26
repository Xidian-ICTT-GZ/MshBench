use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn heap_bytes(ptr: *mut u8, len: usize) = true;

#[predicate]
fn stack_bytes(ptr: *const u8, len: usize) = true;

#[requires(heap_bytes(dst, count) * stack_bytes(src, count))]
#[ensures(heap_bytes(dst, count) * stack_bytes(src, count))]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count * heap_bytes(dst, count) * stack_bytes(src, count))]
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
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
    }
}