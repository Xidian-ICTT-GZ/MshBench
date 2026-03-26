use std::io::{Read, Write, stdin, stdout};

unsafe fn read_byte() -> u8
//@ requires true;
//@ ensures true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ requires true;
//@ ensures true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
//@ requires true;
//@ ensures result != std::ptr::null_mut::<u8>();
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ requires start |-> ?p &*& chars(p, count, ?cs);
//@ ensures start |-> p &*& chars(p, count, cs);
{
    let mut i = 0;
    loop {
        if i == count { break; }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ requires start |-> ?p &*& chars(p, count, ?cs);
//@ ensures start |-> p &*& chars(p, count, cs);
{
    let mut i = 0;
    loop {
        if i == count { break; }
        let b = *start.add(i);
        write_byte(b);
        i += 1;
    }
}

fn main()
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}

/*@
predicate chars(char *p, usize count, list<char> cs) =
    count == length(cs) &*&
    chars_(p, cs);

fixpoint bool chars_(char *p, list<char> cs) {
    switch(cs) {
        case nil: return true;
        case cons(c, cs0): return p |-> c &*& chars_(p + 1, cs0);
    }
}
@*/