use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate u8_array(*mut u8 ptr, usize len; list<u8> vs) =
    if len == 0 then
        emp
    else
        *ptr |-> ?v &*& u8_array(ptr.offset(1), len - 1, ?vs_tail) &*& vs == cons(v, vs_tail);

lemma void u8_array_split(*mut u8 ptr, usize i, usize j, list<u8> vs)
    requires u8_array(ptr, i + j, vs) &*& i <= length(vs);
    ensures u8_array(ptr, i, take(i, vs)) &*& u8_array(ptr.offset(i as isize), j, drop(i, vs));
{
    if i == 0 {
    } else {
        open u8_array(ptr, i + j, vs);
        u8_array_split(ptr.offset(1), i - 1, j, tail(vs));
    }
}

lemma void u8_array_join(*mut u8 ptr, usize i, usize j, list<u8> vs1, list<u8> vs2)
    requires u8_array(ptr, i, vs1) &*& u8_array(ptr.offset(i as isize), j, vs2);
    ensures u8_array(ptr, i + j, append(vs1, vs2));
{
    if i == 0 {
    } else {
        open u8_array(ptr, i, vs1);
        u8_array_join(ptr.offset(1), i - 1, j, tail(vs1), vs2);
    }
}

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    requires [?f]u8_array(src as *mut u8, count, ?vs) &*& u8_array(dst, count, _) &*& count >= 0;
    ensures [f]u8_array(src as *mut u8, count, vs) &*& u8_array(dst, count, vs);
{
    let mut i = 0;
    loop
        invariant [f]u8_array(src as *mut u8, count, vs) &*& u8_array(dst, i, take(i, vs)) &*& u8_array(dst.offset(i as isize), count - i, _) &*& 0 <= i &*& i <= count;
    {
        if i == count {
            break;
        }
        open u8_array(dst.offset(i as isize), count - i, _);
        *dst.add(i) = *src.add(i);
        close u8_array(dst.offset(i as isize), 1, cons(nth(i, vs), nil));
        u8_array_join(dst, i, 1, take(i, vs), cons(nth(i, vs), nil));
        i += 1;
    }
    open u8_array(dst.offset(count as isize), 0, _);
}

fn main() {
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        close u8_array(buffer2, 3, cons(0, cons(0, cons(0, nil))));
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        open u8_array(buffer2, 3, _);
        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        close u8_array(buffer2, 3, cons(10, cons(20, cons(30, nil))));

        dealloc(buffer2, layout);
    }
}