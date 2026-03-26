use std::io::{stdin, stdout, Read, Write};

/*@
predicate array_(start: *mut u8, count: usize;) =
    count == 0 ? emp : 
    (start |-> ?v &*& array_(start + 1, count - 1));
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
predicate alloc_block(p: *mut u8, sz: usize;) = 
    p |-> _ &*& 
    (if sz == 0 then emp else alloc_block(p + 1, sz - 1));

lemma void alloc_block_concrete(void *p, usize sz)
    requires alloc_block(p, sz);
    ensures alloc_block(p, sz);
{
    // no-op, pure ownership predicate unfolding
}

/*@
requires true;
ensures array_(result, count);
@*/
unsafe fn alloc(count: usize) -> *mut u8 {
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
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        //@ open array_(start, count);
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
        //@ close array_(start, count);
    }
}

/*@
requires array_(start, count);
ensures array_(start, count);
@*/
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        //@ open array_(start, count);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close array_(start, count);
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