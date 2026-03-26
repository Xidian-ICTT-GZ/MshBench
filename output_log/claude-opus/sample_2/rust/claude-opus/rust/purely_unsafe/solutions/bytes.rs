use std::io::{stdin, stdout, Read, Write};

/*@
predicate array_(start: *mut u8, count: usize;) =
    count == 0 ? emp : *start |-> _ &*& array_(start + 1, count - 1);
@*/

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

/*@
predicate alloc_array(ptr: *mut u8, n: usize;) =
    n == 0 ? emp : ptr |-> _ &*& alloc_array(ptr + 1, n - 1);

#[requires(true)]
#[ensures(alloc_array(result, count))]
@*/
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

/*@
#[requires(alloc_array(start, count))]
#[ensures(alloc_array(start, count))]
@*/
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        open alloc_array(start, count);
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
        close alloc_array(start, count);
    }
}

/*@
#[requires(alloc_array(start, count))]
#[ensures(alloc_array(start, count))]
@*/
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        open alloc_array(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        close alloc_array(start, count);
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