use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

#[predicate]
fn array8(s: *const u8, n: usize) -> bool {
    exists!{|i: usize| 0 <= i && i < n && s.add(i) is u8}
}

#[predicate]
fn array8_mut(s: *mut u8, n: usize) -> bool {
    exists!{|i: usize| 0 <= i && i < n && s.add(i) is u8}
}

#[requires(array8(src, count))]
#[requires(array8_mut(dst, count))]
#[requires(forall(|i: usize| 0 <= i && i < count ==> src.add(i) != dst.add(i)))]
#[ensures(array8(src, count))]
#[ensures(array8_mut(dst, count))]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(array8(src, count))]
    #[invariant(array8_mut(dst, count))]
    #[invariant(forall(|j: usize| 0 <= j && j < i ==> *dst.add(j) == *src.add(j)))]
    #[invariant(0 <= i && i <= count)]
    loop {
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        #[assert(array8(&raw const buffer1 as *const u8, 3))]
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        #[assert(array8_mut(buffer2, 3))]
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        #[assert(array8_mut(buffer2, 3))]
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        
    }
}