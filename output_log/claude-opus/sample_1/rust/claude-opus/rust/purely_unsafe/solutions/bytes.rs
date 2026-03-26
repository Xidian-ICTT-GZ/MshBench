use std::io::{stdin, stdout, Read, Write};

/*@
predicate array_(start: *mut u8, count: usize;) = 
    count == 0 ? emp : 
    *start |-> _ &*& array_(start + 1, count - 1);
@*/

unsafe fn read_byte() -> u8 
    //@ requires emp;
    //@ ensures emp;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8) 
    //@ requires emp;
    //@ ensures emp;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

/*@
predicate alloc_bytes(ptr: *mut u8, size: usize) = ptr != 0 && ptr |-> ?b &*& array_(ptr, size - 1);

fixpoint bool valid_ptr(void* p) { true }

lemma void alloc_bytes_close(void* p, int size)
    requires p != 0 && malloc_block(p, size);
    ensures alloc_bytes(cast(*mut u8) p, size);
{
    open malloc_block(p, size);
    close alloc_bytes(cast(*mut u8) p, size);
}

/*@
requires true;
ensures alloc_bytes(result, count);
@*/
unsafe fn alloc(count: usize) -> *mut u8
    //@ requires true;
    //@ ensures alloc_bytes(result, count);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close array_(result, count);
    result
}

/*@
requires array_(start, count);
ensures array_(start, count);
@*/
unsafe fn read_bytes(start: *mut u8, count: usize)
    //@ requires array_(start, count);
    //@ ensures array_(start, count);
{
    //@ open array_(start, count);
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
    //@ close array_(start, count);
}

/*@
requires array_(start, count);
ensures array_(start, count);
@*/
unsafe fn write_bytes(start: *mut u8, count: usize)
    //@ requires array_(start, count);
    //@ ensures array_(start, count);
{
    //@ open array_(start, count);
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
    //@ close array_(start, count);
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}