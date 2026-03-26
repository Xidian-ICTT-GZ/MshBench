use std::io::{stdin, stdout, Read, Write};

predicate heap_block(ptr: *mut u8, size: usize) = true;

unsafe fn read_byte() -> u8
    #[ensures(true)]
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    #[requires(true)]
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
    #[requires(count > 0)]
    #[ensures(heap_block(result, count))]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    #[requires(heap_block(start, count))]
    #[ensures(heap_block(start, count))]
{
    let mut i = 0;
    loop
        #[invariant(i <= count && heap_block(start, count))]
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
    #[requires(heap_block(start, count))]
    #[ensures(heap_block(start, count))]
{
    let mut i = 0;
    loop
        #[invariant(i <= count && heap_block(start, count))]
    {
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