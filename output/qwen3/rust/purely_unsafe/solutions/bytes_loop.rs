use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct AllocatedBytes<'a>(ptr: *mut u8, count: usize, @'a);

#[lemma]
#[requires(AllocatedBytes(p, n, @l))]
#[ensures(AllocatedBytes(p, n, @l))]
pub fn alloc_bytes_preserves(p: *mut u8, n: usize, l: &'static ()) {
    // trivial lemma to allow reuse of predicate
}

unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8 {
    #[requires(count > 0)]
    #[ensures(result != std::ptr::null_mut() && AllocatedBytes(result, count, @()))]
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize) {
    #[requires(count > 0 && AllocatedBytes(start, count, @l))]
    #[ensures(AllocatedBytes(start, count, @l))]
    let mut i = 0;
    loop {
        #[invariant(i <= count && AllocatedBytes(start, count, @l))]
        if i == count {
            break;
        }
        let b = read_byte();

        #[requires(i < count && AllocatedBytes(start, count, @l))]
        #[ensures(AllocatedBytes(start, count, @l))]
        *start.add(i) = b;

        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize) {
    #[requires(count > 0 && AllocatedBytes(start, count, @l))]
    #[ensures(AllocatedBytes(start, count, @l))]
    let mut i = 0;
    loop {
        #[invariant(i <= count && AllocatedBytes(start, count, @l))]
        if i == count {
            break;
        }

        #[requires(i < count && AllocatedBytes(start, count, @l))]
        #[ensures(AllocatedBytes(start, count, @l))]
        let b = *start.add(i);

        write_byte(b);
        i += 1 }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        // Note: VeriFast does not require explicit deallocation for this example,
        // but in a full program one would need to free the memory with dealloc.
        // Since the program terminates immediately after, we omit deallocation.
    }
}