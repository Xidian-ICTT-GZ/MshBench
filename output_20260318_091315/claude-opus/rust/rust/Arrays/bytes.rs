use std::io::{Read, Write, stdin, stdout};

predicate byte_ptr(u8 *p, u8 v) = p |-> v;

predicate byte_buffer(u8 *start, usize count, list<u8> vals;) =
    match count {
        0 => emp,
        _ => byte_ptr(start, head(vals)) &*& byte_buffer(start.add(1), count - 1, tail(vals))
    };

#[requires(true)]
#[ensures(result != std::ptr::null_mut() && byte_buffer(result, count, ?vals))]
unsafe fn alloc(count: usize) -> *mut u8
    
    
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(true)]
#[ensures(true)]
unsafe fn read_byte() -> u8
    
    
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8)
    
    
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(byte_buffer(start, count, _))]
#[ensures(byte_buffer(start, count, ?vals))]
unsafe fn read_bytes(start: *mut u8, count: usize)
    
    
    
    
    
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(byte_buffer(start, count, ?vals))]
#[ensures(byte_buffer(start, count, vals))]
unsafe fn write_bytes(start: *mut u8, count: usize)
    
    
{
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
}

fn main()
{
    unsafe {
        let array = alloc(100);
        
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        
    }
}