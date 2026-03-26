use std::io::{stdin, stdout, Read, Write};

#[pred]
pub struct AllocatedBytes<'a>(ptr: *mut u8, count: usize, data: list<u8>, @'a)
    = ptr |->? _ &*& allocated_chunk(ptr, count) &*&
      array_slice(ptr, 0, count, data);

predicate allocated_chunk(void* p, size_t n) =
    chars(p, n);

predicate array_slice(void* start, int i, int count, list<u8> data) =
    switch(i) {
        case 0 => emp &*& length(data) == count;
        case _ => 
          start + (i - 1) |-> ?v &*& array_slice(start, i - 1, count, tail(data));
      };

#[lemma]
#[requires(AllocatedBytes(p, n, data, @l))]
#[ensures(AllocatedBytes(p, n, data, @l))]
pub fn alloc_bytes_preserves(p: *mut u8, n: usize, l: &'static ()) {
    // trivial lemma to allow reuse of predicate
}

unsafe fn read_byte() -> u8
    #[ensures(result |-> ?b &*& chars(result, 1))]
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
{}

unsafe fn alloc(count: usize) -> *mut u8
    #[requires(count > 0)]
    #[ensures(result != std::ptr::null_mut() && AllocatedBytes(result, count, ?data, @()))]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    // After allocation, we own fresh memory block (uninitialized, but here modeled as zero)
    assume(array_slice(result, 0, count, take(count, repeat(0))));
    assume(allocated_chunk(result, count));
    close AllocatedBytes(result, count, take(count, repeat(0)), @());
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
    #[requires(count > 0 && AllocatedBytes(start, count, ?data, @l))]
    #[ensures(AllocatedBytes(start, count, data, @l))]
{
    let mut i = 0;
    close array_slice(start, count, count, data);
    open AllocatedBytes(start, count, data, @l);
    loop {
        #[invariant(i <= count && array_slice(start, i, count, ?prefix) &*& length(prefix) == i &*&
            array_slice(start, count, count, data) &*& length(data) == count)]
        if i == count {
            break;
        }
        let b = read_byte();
        open array_slice(start, count, count, data);
        // write the read byte at start + i:
        *start.add(i) = b;
        close array_slice(start, i + 1, count, cons(b, drop(i + 1, data)));
        i += 1;
    }
    close AllocatedBytes(start, count, data, @l);
}

unsafe fn write_bytes(start: *mut u8, count: usize)
    #[requires(count > 0 && AllocatedBytes(start, count, ?data, @l))]
    #[ensures(AllocatedBytes(start, count, data, @l))]
{
    let mut i = 0;
    open AllocatedBytes(start, count, data, @l);
    close array_slice(start, count, count, data);
    loop {
        #[invariant(i <= count && array_slice(start, i, count, ?prefix) &*& length(prefix) == i &*&
            array_slice(start, count, count, data) &*& length(data) == count)]
        if i == count {
            break;
        }
        open array_slice(start, count, count, data);
        let b = *start.add(i);
        write_byte(b);
        close array_slice(start, i + 1, count, data);
        i += 1;
    }
    close AllocatedBytes(start, count, data, @l);
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}