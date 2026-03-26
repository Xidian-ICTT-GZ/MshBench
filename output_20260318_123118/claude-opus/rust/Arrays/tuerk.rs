use std::io::{Read, Write, stdin, stdout};

predicate byte_array(void* p, int count) = p != null &*& count >= 0 &*& chars(p, count, ?cs) &*& length(cs) == count;

predicate chars<void*> = chars(void* p, int length, list<u8> cs);

fixpoint list<u8> append_byte(list<u8> cs, uint8 b) {
    switch (cs) {
        case nil: return cons(b, nil);
        case cons(h, tail): return cons(h, append_byte(tail, b));
    }
}

fixpoint list<u8> chars(void* p, int length, list<u8> cs);

open spec predicate chars(void* p, int length, list<u8> cs) = 
    length == length(cs) &*&
    (
        length == 0 ? emp :
        p |->? (head) &*&
        chars(p.offset(1), length - 1, tail) &*&
        cs == cons(head, tail)
    );

#[requires(true)]
#[ensures(result != null &*& byte_array(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(true)]
#[ensures(byte_array(?ptr, 1))]
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(byte_array(buf, 1))]
#[ensures(true)]
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(byte_array(start, count))]
#[ensures(byte_array(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(0 <= i &*& i <= count &*& exists<list<u8>>(?cs) &*&
        length(cs) == count &*& 
        chars(start, i, take(i, cs)) &*&
        chars(start.offset(i), count - i, drop(i, cs))
    )]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

#[requires(byte_array(start, count))]
#[ensures(byte_array(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(0 <= i &*& i <= count &*& chars(start, count, ?cs) &*& length(cs) == count)]
    loop {
        if i == count { break; }
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