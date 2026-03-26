use std::io::{Read, Write, stdin, stdout};

predicate bytes_slice(*mut u8 ptr, usize len) = 
    if len == 0 then emp else
        *ptr |-> _ &*& bytes_slice(ptr.offset(1), len - 1);

unsafe fn read_byte() -> u8
    requires emp;
    ensures emp;

{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    requires emp;
    ensures emp;

{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
    requires count <= usize::MAX / std::mem::size_of::<u8>();
    ensures bytes_slice(result, count);

{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    requires bytes_slice(start, count);
    ensures bytes_slice(start, count);

{
    let mut i = 0;
    loop 
        invariant 0 <= i && i <= count &*& bytes_slice(start, i) &*& bytes_slice(start.offset(i as isize), count - i);
    {
        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    requires bytes_slice(start, count);
    ensures bytes_slice(start, count);

{
    let mut i = 0;
    loop 
        invariant 0 <= i && i <= count &*& bytes_slice(start, i) &*& bytes_slice(start.offset(i as isize), count - i);
    {
        if i == count { break; }
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