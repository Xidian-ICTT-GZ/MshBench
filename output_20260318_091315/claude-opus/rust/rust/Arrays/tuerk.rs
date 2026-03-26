use std::io::{Read, Write, stdin, stdout};

predicate byte_ptr(uint8* p) = p |-> _;
predicate bytes_slice(uint8* start, usize count) = start |-> ?b &*&
  if count == 0 { true } else { bytes_slice(start + 1, count - 1) };

#[requires(true)]
#[ensures(byte_ptr(result))]
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(byte_ptr(&value))]
#[ensures(byte_ptr(&value))]
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(bytes_slice(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(bytes_slice(start, count))]
#[ensures(bytes_slice(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(0 <= i && i <= count &*& bytes_slice(start, count))]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

#[requires(bytes_slice(start, count))]
#[ensures(bytes_slice(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(0 <= i && i <= count &*& bytes_slice(start, count))]
    loop {
        if i == count { break; }
        write_byte(*start.add(i));
        i += 1;
    }
}

fn main() {
    unsafe {
        #[predicate]
        predicate allocated_bytes(uint8* p, usize n) = bytes_slice(p, n);

        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}