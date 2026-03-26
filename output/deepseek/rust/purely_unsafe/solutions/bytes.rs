use std::io::{stdin, stdout, Read, Write};

// Predicate for ownership of a single heap-allocated byte
#[predicate]
fn byte_points_to(ptr: *mut u8, value: u8) -> bool {
    unsafe { *ptr == value }
}

// Predicate for ownership of a contiguous heap region
#[predicate]
fn bytes_points_to(start: *mut u8, count: usize) -> bool {
    if count == 0 {
        true
    } else {
        byte_points_to(start, ?val) && bytes_points_to(start.add(1), count - 1)
    }
}

// Specification for alloc: returns ownership of the allocated region
#[requires(count > 0)]
#[ensures(bytes_points_to(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

// Specification for read_byte: consumes no heap, returns a byte
#[ensures(result <= 255)]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

// Specification for write_byte: consumes no heap, writes a byte
#[requires(value <= 255)]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

// Specification for read_bytes: requires ownership of region, fills it with read bytes
#[requires(bytes_points_to(start, count))]
#[ensures(bytes_points_to(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        let b = read_byte();
        #[invariant(bytes_points_to(start, count))]
        {
            *start = b;
            read_bytes(start.add(1), count - 1);
        }
    }
}

// Specification for write_bytes: requires ownership of region, writes its contents
#[requires(bytes_points_to(start, count))]
#[ensures(bytes_points_to(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        #[invariant(bytes_points_to(start, count))]
        {
            let b = *start;
            write_byte(b);
            write_bytes(start.add(1), count - 1);
        }
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