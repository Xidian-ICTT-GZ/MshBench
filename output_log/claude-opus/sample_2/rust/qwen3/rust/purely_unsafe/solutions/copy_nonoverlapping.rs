use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred ptr_block(p: *mut u8, n: usize) = 
    n == 3 &*&
    p |-> ?x0 * p.add(1) |-> ?x1 * p.add(2) |-> ?x2]

#[pred ptr_block_n(p: *mut u8, n: usize) = 
    n == 0 ? emp : p |-> ?x * ptr_block_n(p.add(1), n - 1)]

#[requires(src |-> ?x0 * src.add(1) |-> ?x1 * src.add(2) |-> ?x2 && count == 3)]
#[requires(dst |-> ?y0 * dst.add(1) |-> ?y1 * dst.add(2) |-> ?y2 && count == 3)]
#[ensures(dst |-> x0 * dst.add(1) |-> x1 * dst.add(2) |-> x2 && count == 3)]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(
        i <= count &&
        src |-> ?x0 * src.add(1) |-> ?x1 * src.add(2) |-> ?x2 &&
        dst |-> ?y0 * dst.add(1) |-> ?y1 * dst.add(2) |-> ?y2 &&
        (i == 0 ?
            emp
        :
            // Ownership of first i bytes at dst replaced with copied values
            (
                i == 1 ?
                    dst |-> x0 * dst.add(1) |-> y1 * dst.add(2) |-> y2
                :
                i == 2 ?
                    dst |-> x0 * dst.add(1) |-> x1 * dst.add(2) |-> y2
                :
                i == 3 ?
                    dst |-> x0 * dst.add(1) |-> x1 * dst.add(2) |-> x2
                :
                    emp
            )
        )
    )]
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
        #[assert(buffer2 |-> _ * buffer2.add(1) |-> _ * buffer2.add(2) |-> _)]
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        #[assert(buffer2 |-> 10 * buffer2.add(1) |-> 20 * buffer2.add(2) |-> 30)]
        dealloc(buffer2, layout);
    }
}