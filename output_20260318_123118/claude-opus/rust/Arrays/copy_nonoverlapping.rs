use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate byte_at(void* p, u8 v) = p |-> v;

predicate bytes(void* p, int count, list<u8> vs) =
    count == length(vs) &*&
    count > 0 ?
      byte_at(p, head(vs)) * bytes(p + 1, count - 1, tail(vs))
    :
      true;

#[requires(bytes(src as void*, count, ?vs) * (dst as void*) +-> _ |-> _ * (dst as void*) +-> _ |-> _ ** count > 0 || (count == 0 && true))]
#[requires(count == length(vs))]
#[ensures(bytes(src as void*, count, vs) * bytes(dst as void*, count, vs))]
unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(0 <= i && i <= count &*&
        bytes(src as void* + i, count - i, drop(i, ?vs0)) &*&
        bytes(dst as void* + i, count - i, ?vs1) &*&
        take(i, vs) == reverse(vs1))] 

    loop {
        if i == count { break; }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];

        
        #[assert(bytes(&buffer1 as *const u8 as void*, 3, [10, 20, 30]))]

        let buffer2 = alloc(Layout::from_size_align_unchecked(3, 1));
        if buffer2.is_null() {
            handle_alloc_error(Layout::from_size_align_unchecked(3, 1));
        }

        
        #[assert((buffer2 as void*) +-> _ |-> _ ** 3)]

        copy_nonoverlapping(&buffer1 as *const u8, buffer2, 3);

        
        #[assert(bytes(buffer2 as void*, 3, [10, 20, 30]))]

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, Layout::from_size_align_unchecked(3, 1));
    }
}