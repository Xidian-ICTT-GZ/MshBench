use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn block_sep(ptr: *mut u8, len: usize) -> bool;

unsafe fn copy_nonoverlapping(src: *const u8, dst: *mut u8, count: usize)
    requires(count == 0 || (block_sep(src as *mut u8, count) && block_sep(dst, count)))
    ensures(block_sep(dst, count))
{
    let mut i = 0;
    loop
        invariant(i <= count && block_sep(dst, count) && (i == 0 || block_sep(src as *mut u8, count)))
    {
        if i == count {
            break;
        }
        *dst.add(i) = *src.add(i);
        i += 1;
    }
}

fn main()
    requires(true)
    ensures(true)
{
    unsafe {
        let buffer1: [u8; 3] = [10, 20, 30];
        let layout = Layout::from_size_align_unchecked(3, 1);
        let buffer2 = alloc(layout);
        if buffer2.is_null() {
            handle_alloc_error(layout);
        }
        copy_nonoverlapping(&raw const buffer1 as *const u8, buffer2, 3);

        std::hint::assert_unchecked(*buffer2.add(1) == 20);

        dealloc(buffer2, layout);
    }
}