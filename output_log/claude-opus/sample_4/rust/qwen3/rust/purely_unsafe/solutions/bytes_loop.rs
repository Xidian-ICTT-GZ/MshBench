use std::io::{stdin, stdout, Read, Write};

#[predicate]
pub unsafe fn AllocatedBytes(ptr: *mut u8, count: usize) = 
    count > 0 &*&  // nonempty allocation
    pointer_to_bytes(ptr, count);

#[predicate]
pub unsafe fn pointer_to_bytes(ptr: *mut u8, count: usize) =
    count > 0 &*&
    // Own the range [ptr..ptr+count) as valid bytes
    ^(forall |i: int| 0 <= i && i < count as int ==> true);

#[lemma]
#[requires(AllocatedBytes(p, n))]
#[ensures(AllocatedBytes(p, n))]
pub fn alloc_bytes_preserves(p: *mut u8, n: usize) {
    // trivial lemma to allow reuse of predicate
}

unsafe fn read_byte() -> u8
    #[requires(true)]
    #[ensures(true)]
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    #[requires(true)]
    #[ensures(true)]
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
    #[requires(count > 0)]
    #[ensures(result != std::ptr::null_mut() && AllocatedBytes(result, count))]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    #[requires(count > 0 && AllocatedBytes(start, count))]
    #[ensures(AllocatedBytes(start, count))]
{
    let mut i = 0;
    while i < count
        #[invariant(0 <= i && i <= count && AllocatedBytes(start, count))]
    {
        let b = read_byte();

        // We have ownership of start[i], so we can write the byte
        *(start.add(i)) = b;

        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    #[requires(count > 0 && AllocatedBytes(start, count))]
    #[ensures(AllocatedBytes(start, count))]
{
    let mut i = 0;
    while i < count
        #[invariant(0 <= i && i <= count && AllocatedBytes(start, count))]
    {
        let b = *(start.add(i));
        write_byte(b);
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}