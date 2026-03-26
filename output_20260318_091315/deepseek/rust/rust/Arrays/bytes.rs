use std::io::{Read, Write, stdin, stdout};

/*@
predicate_ctor stdin_state(any info) = true;
predicate_ctor stdout_state(any info) = true;

predicate stdin_io() = 
    stdin_state(()) &*&
    exists<F: future> future(F) &*& F == stdin_state(()) &*&
    true;

predicate stdout_io() = 
    stdout_state(()) &*&
    exists<F: future> future(F) &*& F == stdout_state(()) &*&
    true;

predicate bytes_owned(*mut u8, usize) = 
    [_] &*&
    true;

predicate_ctor byte_owned(pointer: *mut u8, value: u8)() = 
    [_] &*&
    pointer != 0 &*&
    *pointer |-> value;

predicate byte_slice(*mut u8, count: usize) = 
    count == 0 ? 
        emp 
    : 
        byte_owned(pointer, _)() &*& 
        byte_slice(pointer.offset(1), count - 1);
@*/

#[requires(stdin_io())]
#[ensures(stdin_io())]
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(stdout_io())]
#[ensures(stdout_io())]
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(result != 0)]
#[ensures(bytes_owned(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(bytes_owned(start, count))]
#[ensures(bytes_owned(start, count))]
#[requires(stdin_io())]
#[ensures(stdin_io())]
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(bytes_owned(start, count))]
#[ensures(bytes_owned(start, count))]
#[requires(stdout_io())]
#[ensures(stdout_io())]
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
}

#[requires(stdin_io())]
#[requires(stdout_io())]
#[ensures(stdin_io())]
#[ensures(stdout_io())]
fn main()
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}