use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

//@ pred slice_uf(u8* p, usize len; list<u8> vs) = p |-> ?v &*& vs == cons(v, ?vs0) &*& slice_uf(p + 1, len - 1; vs0)
//@                                                                 || (len == 0 &*& vs == nil);

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
//@ requires chars(src, count, ?vs) &*& chars(dst, count, _);
//@ ensures chars(src, count, vs) &*& chars(dst, count, vs);
{
    let mut i = 0;
    loop {
        //@ if i < count { open chars(src + i, 1, ?v1); open chars(dst + i, 1, ?v2); }

        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;

        //@ if i <= count { close chars(dst + i - 1, 1, v1); close chars(src + i - 1, 1, v1); }
    }
}

//@ predicate chars(void* p, usize count, list<u8> vs) = 
//@     count == 0 ? vs == nil : p |-> ?v &*& vs == cons(v, ?vs0) &*& chars(p + 1, count - 1, vs0);

fn main()
{
    unsafe {
        let buffer1: [u8; _] = [10, 20, 30];
        //@ close chars(buffer1.as_ptr() as *const u8, 3, [10,20,30]);
        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }
        //@ close chars(buffer2, 3, [_,_,_]); // uninitialized memory
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);
        //@ open chars(buffer2, 3, ?vs_copied); assert(vs_copied == [10,20,30]);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);
        
        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
    }
}