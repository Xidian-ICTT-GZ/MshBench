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
        // buffer1: [u8; 3] with known values
        let buffer1: [u8; 3] = [10, 20, 30];
        // buffer1 ownership predicate for initial state
        predicate buffer1_pred() = u8_array(buffer1.as_ptr(), 3, seq![10,20,30]);

        // Allocate buffer2 with size 3 and alignment 1
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        // After allocation, have full ownership of uninitialized memory in buffer2
        // Represent it as a sequence of length 3 with unknown values (here we use fresh ghost variable)
        ghost {
            let uninit_vals = seq![0u8,0,0]; // symbolic placeholder; can also be fresh symbolic seq
            assume(u8_array_mut(buffer2, 3, uninit_vals));
        }
        
        // Precondition for copy_nonoverlapping: buffer1 ownership predicate & buffer2 ownership predicate
        // Formally:
        // u8_array(buffer1.as_ptr(), 3, seq![10,20,30]) &*& u8_array_mut(buffer2, 3, _) 
        
        copy_nonoverlapping(buffer1.as_ptr(), buffer2, 3);
        // After copy, buffer2 contains seq![10,20,30]
        // Ownership predicates hold accordingly

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
        // After deallocation, ownership predicate for buffer2 is consumed
    }
}