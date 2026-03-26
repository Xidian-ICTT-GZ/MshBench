use std::io::{stdin, stdout, Read, Write};

predicate buffer_block(ptr: *mut u8, len: usize) =
  ptr |-> ?v &*& buffer_block_bytes(ptr + 1, len - 1) if len > 0
  ;
predicate buffer_block_bytes(ptr: *mut u8, len: usize) =
  match len {
    0 => emp,
    _ => ptr |-> ?v &*& buffer_block_bytes(ptr + 1, len - 1)
  }
;

#[requires(true)]
#[ensures(true)]
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
#[ensures(buffer_block(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(buffer_block(start, count))]
#[ensures(buffer_block(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        #[invariant(buffer_block(start, count) &*& i <= count)]
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

#[requires(buffer_block(start, count))]
#[ensures(buffer_block(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i = 0;
    loop {
        #[invariant(buffer_block(start, count) &*& i <= count)]
        {
            if i == count {
                break;
            }

            let b = *start.add(i);

            write_byte(b);
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