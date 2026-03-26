use std::io::{stdin, stdout, Read, Write};

/*@
predicate array_(start: *mut u8, count: usize) = 
    count == 0 ? emp : *start |-> _ &*& array_(start + 1, count - 1);
@*/

unsafe fn read_byte() -> u8
    #[requires true]
    #[ensures true]
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
    #[requires true]
    #[ensures true]
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

/*@
predicate_allocs_alloc(result: *mut u8, count: usize) = true; 
@*/
/*@
lemma void array_alloc_lemma(*p: pointer, count: usize)
    requires true;
    ensures array_(p, count);
{
    if (count > 0) {
        open array_(p, count);
        array_alloc_lemma(p + 1, count - 1);
        close array_(p, count);
    }
}
@*/

/*@
predicate alloc_block(ptr: *mut u8, size: usize) = 
    ptr != null &*& malloc_block(ptr, size);
@*/

/*@
fixpoint bool is_aligned(void* ptr, usize align) {
    return (usize(ptr) % align) == 0;
}
@*/

/*@
predicate array_alloc(start: *mut u8, count: usize) = 
    alloc_block(start, count) &*& array_(start, count);
@*/

/*@
@*/
unsafe fn alloc(count: usize) -> *mut u8
    #[requires true]
    #[ensures array_alloc(result, count)]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close alloc_block(result, count);
    //@ close array_(result, count);
    result
}

/*@
unsafe fn read_bytes(start: *mut u8, count: usize)
    requires array_(start, count);
    ensures array_(start, count);
{
    open array_(start, count);
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
    close array_(start, count);
}
@*/

/*@
unsafe fn write_bytes(start: *mut u8, count: usize)
    requires array_(start, count);
    ensures array_(start, count);
{
    open array_(start, count);
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
    close array_(start, count);
}
@*/

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}