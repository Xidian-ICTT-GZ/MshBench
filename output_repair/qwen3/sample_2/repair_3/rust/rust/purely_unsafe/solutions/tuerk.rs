use std::io::{stdin, stdout, Read, Write};

predicate bytes_slice(*mut u8 start, usize count) =
    if count == 0 then
        emp
    else
        *start |-> _ &*& bytes_slice(start.offset(1), count - 1);

unsafe fn read_byte() -> u8
    ensures true
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    requires true
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
    requires count > 0,
    ensures bytes_slice(result, count)
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    requires bytes_slice(start, count),
    ensures bytes_slice(start, count)
{
    let mut i = 0;
    loop
        invariant 0 <= i && i <= count &*& bytes_slice(start, count)
        decreases count - i
    {
        if i == count {
            break;
        }
        let b = read_byte();
        *start.offset(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    requires bytes_slice(start, count),
    ensures bytes_slice(start, count)
{
    let mut i = 0;
    loop
        invariant 0 <= i && i <= count &*& bytes_slice(start, count)
        decreases count - i
    {
        if i == count {
            break;
        }
        write_byte(*start.offset(i));
        i += 1;
    }
}

fn main()
    requires true,
    ensures true
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}