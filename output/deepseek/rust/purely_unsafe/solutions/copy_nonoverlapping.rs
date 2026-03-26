use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn u8_slice(ptr: *const u8, len: usize) -> bool {
    exists(|i: usize| 0 <= i && i <= len && 
        forall(|j: usize| 0 <= j && j < i ==> exists(|v: u8| ptr.add(j)@v)) &&
        forall(|j: usize| i <= j && j < len ==> ptr.add(j)@?))
}

#[predicate]
fn u8_slice_mut(ptr: *mut u8, len: usize) -> bool {
    exists(|i: usize| 0 <= i && i <= len && 
        forall(|j: usize| 0 <= j && j < i ==> exists(|v: u8| ptr.add(j)@v)) &&
        forall(|j: usize| i <= j && j < len ==> ptr.add(j)@?))
}

#[predicate]
fn full_u8_slice(ptr: *const u8, len: usize) -> bool {
    forall(|j: usize| 0 <= j && j < len ==> exists(|v: u8| ptr.add(j)@v))
}

#[predicate]
fn full_u8_slice_mut(ptr: *mut u8, len: usize) -> bool {
    forall(|j: usize| 0 <= j && j < len ==> exists(|v: u8| ptr.add(j)@v))
}

#[requires(
    full_u8_slice(src, count) && 
    u8_slice_mut(dst, count) && 
    src != dst && 
    count > 0 &&
    (src.add(count) <= dst || dst.add(count) <= src)
)]
#[ensures(
    full_u8_slice(src, count) && 
    full_u8_slice_mut(dst, count) &&
    forall(|j: usize| 0 <= j && j < count ==> 
        exists(|v: u8| src.add(j)@v && dst.add(j)@v))
)]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(
        i <= count &&
        full_u8_slice(src, count) &&
        u8_slice_mut(dst, count) &&
        forall(|j: usize| 0 <= j && j < i ==> 
            exists(|v: u8| src.add(j)@v && dst.add(j)@v)) &&
        forall(|j: usize| i <= j && j < count ==> dst.add(j)@?)
    )]
    loop {
        if i == count {
            break;
        }
        let val = *src.add(i);
        *dst.add(i) = val;
        i += 1;
    }
}

#[predicate]
fn array_owned<T>(arr: &[T; N]) -> bool {
    exists(|i: usize| 0 <= i && i <= N &&
        forall(|j: usize| 0 <= j && j < i ==> exists(|v: T| &arr[j]@v)) &&
        forall(|j: usize| i <= j && j < N ==> &arr[j]@?))
}

#[predicate]
fn full_array_owned<T>(arr: &[T; N]) -> bool {
    forall(|j: usize| 0 <= j && j < N ==> exists(|v: T| &arr[j]@v))
}

#[predicate]
fn alloc_owned(ptr: *mut u8, layout: Layout) -> bool {
    layout.size() > 0 && layout.align() > 0 &&
    exists(|i: usize| 0 <= i && i <= layout.size() &&
        forall(|j: usize| 0 <= j && j < i ==> exists(|v: u8| ptr.add(j)@v)) &&
        forall(|j: usize| i <= j && j < layout.size() ==> ptr.add(j)@?))
}

#[predicate]
fn full_alloc_owned(ptr: *mut u8, layout: Layout) -> bool {
    layout.size() > 0 && layout.align() > 0 &&
    forall(|j: usize| 0 <= j && j < layout.size() ==> exists(|v: u8| ptr.add(j)@v))
}

fn main() {
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        #[invariant(full_array_owned(&buffer1))]
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        #[invariant(
            if buffer2.is_null() {
                true
            } else {
                alloc_owned(buffer2, layout)
            }
        )]
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        
        #[invariant(full_array_owned(&buffer1))]
        #[invariant(alloc_owned(buffer2, layout))]
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        #[invariant(full_alloc_owned(buffer2, layout))]
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        #[invariant(full_alloc_owned(buffer2, layout))]
        dealloc(buffer2, layout);
    }
}