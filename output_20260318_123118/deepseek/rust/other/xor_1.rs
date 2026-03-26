use std::io::{Read, Write, stdin, stdout};

#[predicate]
fn u8_slice(ptr: *mut u8, count: usize) -> bool {
    exists!{|i: usize| 0 <= i && i < count && ptr.add(i) |-> ?val}
}

#[predicate]
fn full_u8_slice(ptr: *mut u8, count: usize) -> bool {
    if count == 0 {
        emp
    } else {
        ptr |-> ?val && full_u8_slice(ptr.add(1), count - 1)
    }
}

#[predicate]
fn alloc_u8_slice(ptr: *mut u8, count: usize) -> bool {
    exists!{|layout: std::alloc::Layout| 
        layout.size() == count && layout.align() == 1 && 
        ptr points_to_block(layout) && full_u8_slice(ptr, count)
    }
}

unsafe fn read_byte() -> u8
#[ensures(result == old(stdin())?)]
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
#[requires(old(stdout())?)]
#[ensures(emp)]
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
#[requires(count > 0)]
#[ensures(result != 0 as *mut u8 && alloc_u8_slice(result, count))]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
#[requires(count > 0 && start != 0 as *mut u8)]
#[requires(full_u8_slice(start, count))]
#[ensures(full_u8_slice(start, count))]
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
#[requires(count > 0 && text != 0 as *mut u8 && key != 0 as *mut u8)]
#[requires(full_u8_slice(text, count) && full_u8_slice(key, count))]
#[ensures(full_u8_slice(text, count) && full_u8_slice(key, count))]
{
    if count > 0 {
        let t = *text;
        let k = *key;
        *text = t ^ k;
        xor_bytes(text.add(1), key.add(1), count - 1);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
#[requires(count > 0 && start != 0 as *mut u8)]
#[requires(full_u8_slice(start, count))]
#[ensures(emp)]
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
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
    }
}