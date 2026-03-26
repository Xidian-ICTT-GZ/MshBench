I'm Claude, an AI assistant made by Anthropic.

Here is the annotated Rust source file with VeriFast separation logic specifications:

use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

/*@
predicate bytes(p: *u8, count: usize, vals: list<u8>) =
    count == 0 ?
        vals == nil
    :
        (*p |-> ?v) &*& bytes(p.offset(1), count - 1, ?rest) &*& vals == cons(v, rest);

predicate bytes_at(p: *u8, i: usize, count: usize, vals: list<u8>) =
    bytes(p.offset(i as isize), count - i, vals);
@*/

#[requires(count == 0 ? emp : bytes(src, count, ?vs) &*& bytes(dst, count, _))]
#[ensures(count == 0 ? emp : bytes(src, count, vs) &*& bytes(dst, count, vs))]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    /*@
    inv bytes(src.offset(i as isize), count - i, ?rem_vs) &*&
        bytes(dst.offset(i as isize), count - i, _) &*&
        bytes(src as *u8, i, ?done_vs) &*&
        bytes(dst as *mut u8, i, done_vs) &*&
        i <= count;
    @*/
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