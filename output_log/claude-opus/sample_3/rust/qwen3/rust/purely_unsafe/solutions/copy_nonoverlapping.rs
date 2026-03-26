use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
ptr_block(p: *mut u8, n: usize) = 
    n == 3 && p |-> ?x0 * p.add(1) |-> ?x1 * p.add(2) |-> ?x2;

#[predicate]
ptr_block_n(p: *mut u8, n: usize) = 
    n == 0 ? emp : p |-> _ * ptr_block_n(p.add(1), n - 1);

#[requires(count == 3)]
#[requires(src |-> ?x0 * src.add(1) |-> ?x1 * src.add(2) |-> ?x2)]
#[requires(dst |-> ?y0 * dst.add(1) |-> ?y1 * dst.add(2) |-> ?y2)]
#[ensures(dst |-> x0 * dst.add(1) |-> x1 * dst.add(2) |-> x2)]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count &&
        // src bytes are untouched
        src |-> ?sx0 * src.add(1) |-> ?sx1 * src.add(2) |-> ?sx2 &&
        // dst bytes ownership adjust according to i
        (i == 0 ? (
            dst |-> ?dy0 * dst.add(1) |-> ?dy1 * dst.add(2) |-> ?dy2
        ) : (
            dst |-> (if i>=1 { sx0 } else { dy0 }) *
            (i >= 2 ? dst.add(1) |-> sx1 : dst.add(1) |-> (if i==1 { dy1 } else { dy1 })) *
            (i >= 3 ? dst.add(2) |-> sx2 : dst.add(2) |-> dy2)
        ))
    )]
    loop {
        if i == count {
            break;
        }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

#[requires(true)]
#[ensures(true)]
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