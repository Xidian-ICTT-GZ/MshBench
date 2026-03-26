use std::io::{stdin, stdout, Read, Write};

pred bytes(ptr: *mut u8, count: usize; vs: list<u8>) =
    count == 0 ?
        vs == nil
    :
        ptr |-> ?b &*& bytes(ptr.add(1), count - 1; ?vs0) &*& vs == cons(b, vs0);

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(bytes(result, count; _))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(bytes(start, count; _))]
#[ensures(bytes(start, count; _))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        #[invariant(bytes(start, count; _) &*& 0 <= i &*& i <= count)]
        {
            if i == count {
                break;
            }
            let b = read_byte();
            *start.add(i) = b;
            i += 1;
        }
    }
}

#[requires(bytes(start, count; _))]
#[ensures(bytes(start, count; _))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        #[invariant(bytes(start, count; _) &*& 0 <= i &*& i <= count)]
        {
            if i == count {
                break;
            }

            write_byte(*start.add(i));
            i += 1;
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