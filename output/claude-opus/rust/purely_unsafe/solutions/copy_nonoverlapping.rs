use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate u8_array(ptr: *const u8, count: usize; values: seq<u8>) =
    count == 0 ?
        values == seq_nil() :
        *ptr |-> seq_head(values) &*& u8_array(ptr.add(1), count - 1, seq_tail(values)) &*& seq_length(values) == count;

predicate u8_array_mut(ptr: *mut u8, count: usize; values: seq<u8>) =
    count == 0 ?
        values == seq_nil() :
        *ptr |-> seq_head(values) &*& u8_array_mut(ptr.add(1), count - 1, seq_tail(values)) &*& seq_length(values) == count;

#[requires(u8_array(src, count, ?src_vals) &*& u8_array_mut(dst, count, ?dst_vals))]
#[ensures(u8_array(src, count, src_vals) &*& u8_array_mut(dst, count, src_vals))]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count &*& 
                u8_array(src, count, src_vals) &*& 
                u8_array_mut(dst.add(i), count - i, ?rest_vals) &*&
                u8_array_mut(dst, i, seq_take(src_vals, i)))]
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
        let buffer1: [u8; _] = [10, 20, 30];
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
    }
}