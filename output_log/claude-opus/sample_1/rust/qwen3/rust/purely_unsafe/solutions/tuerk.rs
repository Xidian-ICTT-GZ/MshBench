use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct BytesPred(start: *mut u8, len: usize, data: [u8]) = 
    len == data.len() &*&
    start != std::ptr::null_mut() &*&
    malloc_block(start, len) &*&
    (forall |i: int| 0 <= i && i < len ==> *start.offset(i) |-> data[i]);

#[pred]
pub struct AllocatedBytes(start: *mut u8, len: usize) = 
    start != std::ptr::null_mut() &*&
    malloc_block(start, len);

#[lemma]
#[requires(BytesPred(p, n, data))]
#[ensures(BytesPred(p, n, data))]
pub fn bytes_pred_identity(p: *mut u8, n: usize, data: &[u8]) {}

#[lemmas_for(AllocatedBytes)]
#[requires(AllocatedBytes(p, n))]
#[ensures(AllocatedBytes(p, n))]
pub fn allocated_bytes_lemmas(p: *mut u8, n: usize) {}

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
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
        i <= count &&
        AllocatedBytes(start, count) &&
        BytesPred(start, i, ?prefix)
    )]
    loop {
        if i == count {
            break;
        }
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
        i <= count &&
        BytesPred(start, count, data) &&
        AllocatedBytes(start, count)
    )]
    loop {
        if i == count {
            break;
        }
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