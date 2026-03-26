use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ requires pointer(src, count) &*& pointer_mut(dst, count);
//@ ensures pointer_mut(dst, count);
//@ pred pointer(const void* p, usize n) = n == 0 ? true : p |-> _ &*& pointer(p + 1, n - 1);
//@ pred pointer_mut(void* p, usize n) = n == 0 ? true : p |-> _ &*& pointer_mut(p + 1, n - 1);
{
    let mut i = 0;
    while i < count
    //@ invariant 0 <= i && i <= count &*& pointer(src.add(i), count - i) &*& pointer_mut(dst.add(i), count - i);
    {
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
{
    unsafe {
        //@ predicate buffer_slice(u8* p, int n, list<u8> vs) = n == 0 ? true : p |-> ?v &*& buffer_slice(p + 1, n - 1, ?tail) &*& vs == cons(v, tail);
        let buffer1: [u8; _] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        //@ close pointer(buffer1.as_ptr(), 3);
        //@ close pointer_mut(buffer2, 3);
        copy_nonoverlapping(buffer1.as_ptr(), buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, layout);
    }
}