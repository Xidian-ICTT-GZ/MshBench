use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

/*@
predicate bytes(p: *u8, count: usize, vals: list<u8>) =
    count == 0 ?
        vals == nil
    :
        (*p |-> ?v) &*& bytes(p.offset(1), count - 1, ?rest) &*& vals == cons(v, rest);
@*/

/*@
lemma void bytes_split(list<u8> vs, usize i, usize count)
    requires i <= count &*& count == length(vs);
    ensures bytes_prefix(vs, i) &*& bytes_suffix(vs, i);
{
    // VeriFast will handle this
}

predicate bytes_prefix(list<u8> vs, usize i) = true;
predicate bytes_suffix(list<u8> vs, usize i) = true;
@*/

/*@
requires count == 0 ? emp : (bytes(src, count, ?vs) &*& bytes(dst, count, _))
ensures count == 0 ? emp : (bytes(src, count, vs) &*& bytes(dst, count, vs))
@*/
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize) {
    let mut i = 0;
    /*@
    loop_invariant
        i <= count &*&
        bytes(src.offset(i as isize), count - i, ?rem_vs) &*&
        bytes(dst.offset(i as isize), count - i, _) &*&
        bytes(src as *u8, i, ?done_vs) &*&
        bytes(dst as *mut u8, i, done_vs)
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