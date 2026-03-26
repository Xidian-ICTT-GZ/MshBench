use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct BytesPred(p: *mut u8, len: usize, data: [u8]) = 
    len > 0 ?
        p |-> ?_ &*& array_chunks(p, len, data)
    :
        true;

#[pred]
pub struct AllocatedBytes(p: *mut u8, len: usize) = 
    p != std::ptr::null_mut() &*& len > 0 &*& malloc_block(p, len);

#[lemma]
#[requires(BytesPred(p, n, data))]
#[ensures(BytesPred(p, n, data))]
pub fn bytes_pred_identity(p: *mut u8, n: usize, data: &[u8]) {}

#[lemmas_for(AllocatedBytes)]
#[requires(AllocatedBytes(p, n))]
#[ensures(AllocatedBytes(p, n))]
pub fn allocated_bytes_lemmas(p: *mut u8, n: usize) {}

// Helper predicate: array_chunks ownership of data bytes
#[predicate]
pub fn array_chunks(p: *mut u8, len: usize, data: [u8]) = 
    len == 0 ?
        true
    :
        p |-> data[0] &*& array_chunks(p.offset(1), len - 1, slice(data, 1, len));

#[predicate]
pub fn malloc_block(start: *mut u8, size: usize) = true; // represents heap-allocated block of size

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
    #[requires(AllocatedBytes(start, count))]
    #[ensures(BytesPred(start, count, ?data) && AllocatedBytes(start, count))]
{
    let mut i = 0;
    #[invariant(
        i <= count &*& 
        AllocatedBytes(start, count) &*& 
        BytesPred(start, i, ?prefix)
    )]
    while i < count {
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    #[requires(BytesPred(start, count, ?data) && AllocatedBytes(start, count))]
    #[ensures(BytesPred(start, count, data) && AllocatedBytes(start, count))]
{
    let mut i = 0;
    #[invariant(
        i <= count &*& 
        BytesPred(start, count, data) &*& 
        AllocatedBytes(start, count)
    )]
    while i < count {
        write_byte(*start.add(i));
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