use std::io::{Read, Write, stdin, stdout};

predicate stdin_resource();
predicate stdout_resource();

predicate block(*mut u8 ptr, usize len) =
    match len {
        0 => true,
        _ => *ptr |-> ?v &*& block(ptr.add(1), len - 1)
    };

unsafe fn read_byte() -> u8
    requires stdin_resource();
    ensures stdin_resource() &*& result |-> _;

{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    requires stdout_resource();
    ensures stdout_resource();

{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
    requires true;
    ensures block(result, count);

{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    requires block(start, count) &*& stdin_resource();
    ensures block(start, count) &*& stdin_resource();

{
    
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    requires block(start, count) &*& stdout_resource();
    ensures block(start, count) &*& stdout_resource();

{
    if count > 0 {
        
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        
    }
}

fn main()
    requires stdin_resource() &*& stdout_resource();
    ensures stdin_resource() &*& stdout_resource();

{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        
    }
}