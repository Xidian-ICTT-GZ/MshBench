use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

#[predicate]
fn array8_pointer(ptr: *const u8, len: usize) -> bool {
    exists(|slice: &[u8]| slice.as_ptr() == ptr && slice.len() == len)
}

#[predicate]
fn array8_mut_pointer(ptr: *mut u8, len: usize) -> bool {
    exists(|slice: &mut [u8]| slice.as_mut_ptr() == ptr && slice.len() == len)
}

#[predicate]
fn points_to_bytes(ptr: *const u8, len: usize) -> bool {
    exists(|bytes: &[u8]| bytes.as_ptr() == ptr && bytes.len() == len)
}

#[predicate]
fn points_to_bytes_mut(ptr: *mut u8, len: usize) -> bool {
    exists(|bytes: &mut [u8]| bytes.as_mut_ptr() == ptr && bytes.len() == len)
}

#[requires(
    points_to_bytes(src, count) &&
    points_to_bytes_mut(dst, count) &&
    src != dst as *const u8 &&
    !src.offset(count as isize).overlaps(dst, count)
)]
#[ensures(
    points_to_bytes(src, count) &&
    points_to_bytes_mut(dst, count) &&
    forall(|i: usize| 0 <= i && i < count ==> 
        exists(|v: u8| v == *src.offset(i as isize) && v == *dst.offset(i as isize)))
)]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(
        points_to_bytes(src, count) &&
        points_to_bytes_mut(dst, count) &&
        i <= count &&
        forall(|j: usize| 0 <= j && j < i ==> 
            *dst.offset(j as isize) == *src.offset(j as isize))
    )]
    loop {
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

#[requires(layout.size() > 0 && layout.align() > 0)]
#[ensures(
    if result.is_null() {
        true
    } else {
        points_to_bytes_mut(result, layout.size())
    }
)]
unsafe fn allocate_buffer(layout: Layout) -> *mut u8 {
    let ptr = alloc(layout);
    if ptr.is_null() {
        handle_alloc_error(layout);
    }
    ptr
}

#[requires(points_to_bytes_mut(ptr, layout.size()))]
#[ensures(true)]
unsafe fn deallocate_buffer(ptr: *mut u8, layout: Layout) {
    dealloc(ptr, layout);
}

fn main() {
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        #[assert(points_to_bytes(buffer1.as_ptr(), 3))]
        
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = allocate_buffer(layout);
        
        copy_nonoverlapping(buffer1.as_ptr(), buffer2, 3);
        
        #[assert(*buffer2.add(1) == 20)]
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        deallocate_buffer(buffer2, layout);
    }
}