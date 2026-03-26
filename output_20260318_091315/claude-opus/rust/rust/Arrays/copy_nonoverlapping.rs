use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate array_slice(predicate(usize, u8) elem, void *ptr, usize start, usize len) =
    len == 0 ?
        emp
    :
        ptr |-> ?v &*&
        elem(start, v) &*&
        array_slice(elem, ptr + 1, start + 1, len - 1);

predicate buffer_bytes(void *ptr, usize len, list<u8> bytes) =
    len == 0 ?
        emp
    :
        ptr |-> ?b &*&
        head(bytes) == b &*&
        buffer_bytes(ptr + 1, len - 1, tail(bytes));

#[requires(src_bytes: list<u8>, dst: void *dst, count: usize) 
    &*& buffer_bytes(src, count, src_bytes) &*& buffer_bytes(dst, count, ?dst_bytes)]
#[requires(count <= length(src_bytes))]
#[ensures(buffer_bytes(dst, count, take(count, src_bytes)))]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    //@ decreases count
{
    let mut i = 0;
    #[invariant(i <= count &*& 
        buffer_bytes(src + i, count - i, drop(i, src_bytes)) &*& 
        buffer_bytes(dst + i, count - i, drop(i, dst_bytes)))]
    loop {
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        fixpoint list<u8> slice_to_list(&[u8] slice) {
            switch(slice) {
                case []: return nil;
                case cons(x, xs): return cons(x, slice_to_list(xs));
            }
        }
        let src_bytes = slice_to_list(&buffer1);
        let count = 3;
        let layout = Layout::from_size_align_unchecked(count, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        assume(buffer_bytes(buffer2, count, repeat(0, count))); 

        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, count);

        

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, layout);
    }
}