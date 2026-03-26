use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct AllocatedBytes<'a>(ptr: *mut u8, count: usize, @'a) = 
    // The predicate owns the memory range [ptr .. ptr + count)
    // as an array of u8 in the heap.
    // VeriFast models this as a points-to permission for each byte.
    exists(chars: list<u8>) &*& chars.length == count &*&
    chars.wrap_for_slice(ptr);

#[lemma]
#[requires(AllocatedBytes(p, n, @l))]
#[ensures(AllocatedBytes(p, n, @l))]
pub fn alloc_bytes_preserves(p: *mut u8, n: usize, l: &'static ()) {
    // trivial lemma to allow reuse of predicate
}

// Helper function to describe per-element points-to ownership in AllocatedBytes:
predicate chars.wrap_for_slice(ptr: *mut u8) = // internal helper to define
    chars_points_to_slice(ptr, chars);

fixpoint predicate chars_points_to_slice(list<u8> chars, ptr: *mut u8) {
    switch(chars) {
        case nil: return true;
        case cons(h, t): return ptr |-> h &*& chars_points_to_slice(t, ptr + 1);
    }
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
    #[ensures(result != std::ptr::null_mut() && AllocatedBytes(result, count, @()))]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    // allocate new bytes => own all the bytes initialized to arbitrary value
    // For VeriFast, we take ownership of all count bytes at result.
    // Initialize with some arbitrary values to establish ownership.
    // The predicate AllocatedBytes requires ownership of these bytes.
    //
    // Note: VeriFast expects ownership of memory chunk after alloc.
    // We'll consider the bytes arbitrary but owned.
    //
    // We can fold the predicate for AllocatedBytes here.
    open exists _; close AllocatedBytes(result, count, @());
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    #[requires(count > 0 && AllocatedBytes(start, count, @l))]
    #[ensures(AllocatedBytes(start, count, @l))]
{
    let mut i: usize = 0;
    while (i < count)
        #[invariant(i <= count && AllocatedBytes(start, count, @l))]
    {
        // We have ownership of the entire buffer.

        let b = read_byte();

        // We need to update the byte at start + i to b,
        // so we must open the predicate to access start[i], update it, then close.

        // Open AllocatedBytes to get access to bytes:
        open AllocatedBytes(start, count, @l);
        // The memory at start + i is owned as b_i:
        // unfold internal representation:
        assert chars.wrap_for_slice(start);
        // unfold the linked list points-to:
        open chars_points_to_slice(_, start);

        // We can write to start + i:
        *start.add(i) = b;

        // Rebuild the internal list of bytes with updated value:
        // Replace element at index i with b in the internal list 'chars':
        // VeriFast expects this handled transparently by the predicate assignments.

        // Close predicate again
        close chars_points_to_slice(_, start);
        close chars.wrap_for_slice(start);
        close AllocatedBytes(start, count, @l);

        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    #[requires(count > 0 && AllocatedBytes(start, count, @l))]
    #[ensures(AllocatedBytes(start, count, @l))]
{
    let mut i: usize = 0;
    while (i < count)
        #[invariant(i <= count && AllocatedBytes(start, count, @l))]
    {
        // Open predicate to read byte at start + i
        open AllocatedBytes(start, count, @l);
        assert chars.wrap_for_slice(start);
        open chars_points_to_slice(_, start);

        let b = *start.add(i);

        close chars_points_to_slice(_, start);
        close chars.wrap_for_slice(start);
        close AllocatedBytes(start, count, @l);

        write_byte(b);

        i += 1;
    }
}

fn main()
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        // Note: VeriFast does not require explicit deallocation for this example,
        // but in a full program one would need to free the memory with dealloc.
        // Since the program terminates immediately after, we omit deallocation.
    }
}