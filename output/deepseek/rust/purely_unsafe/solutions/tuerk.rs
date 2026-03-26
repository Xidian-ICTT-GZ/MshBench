use std::io::{stdin, stdout, Read, Write};

// Predicate for ownership of a single byte at pointer p
predicate ptr_byte(p: *mut u8, v: u8) {
    |p| -> bool { true } && true
}

// Predicate for ownership of a contiguous block of bytes
predicate bytes(p: *mut u8, count: usize) {
    if count == 0 {
        true
    } else {
        ptr_byte(p, ?v) * bytes(p.offset(1), count - 1)
    }
}

#[requires(true)]
#[ensures(result != 0)]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(bytes(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(bytes(start, count))]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

#[requires(bytes(start, count))]
#[ensures(bytes(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(bytes(start, count))]
    loop {
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