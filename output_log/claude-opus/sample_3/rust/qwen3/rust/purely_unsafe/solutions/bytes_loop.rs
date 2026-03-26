use std::io::{stdin, stdout, Read, Write};

/*@
pred AllocatedBytes(ptr: *mut u8, count: usize;) =
    alloc_block(ptr, count) &*& chars_(ptr, count, _);
@*/

/*@
lem alloc_bytes_split(ptr: *mut u8, i: usize, count: usize)
    req AllocatedBytes(ptr, count) &*& 0 <= i &*& i < count;
    ens chars_(ptr, i, _) &*& char_(ptr + i, _) &*& chars_(ptr + i + 1, count - i - 1, _) &*& alloc_block(ptr, count);
{
    open AllocatedBytes(ptr, count);
    chars__split(ptr, i);
    open chars_(ptr + i, count - i, _);
}
@*/

/*@
lem alloc_bytes_join(ptr: *mut u8, i: usize, count: usize)
    req chars_(ptr, i, _) &*& char_(ptr + i, _) &*& chars_(ptr + i + 1, count - i - 1, _) &*& alloc_block(ptr, count) &*& 0 <= i &*& i < count;
    ens AllocatedBytes(ptr, count);
{
    close chars_(ptr + i, count - i, _);
    chars__join(ptr);
    close AllocatedBytes(ptr, count);
}
@*/

#[ensures(true)]
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[ensures(true)]
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(AllocatedBytes(result, count))]
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close AllocatedBytes(result, count);
    result
}

#[requires(count > 0 &*& AllocatedBytes(start, count))]
#[ensures(AllocatedBytes(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
    let mut i: usize = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& AllocatedBytes(start, count);
        if i == count {
            break;
        }
        let b = read_byte();
        //@ alloc_bytes_split(start, i, count);
        *start.add(i) = b as i8;
        //@ alloc_bytes_join(start, i, count);
        i += 1;
    }
}

#[requires(count > 0 &*& AllocatedBytes(start, count))]
#[ensures(AllocatedBytes(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
    let mut i: usize = 0;
    loop {
        //@ inv 0 <= i &*& i <= count &*& AllocatedBytes(start, count);
        if i == count {
            break;
        }
        //@ alloc_bytes_split(start, i, count);
        let b = *start.add(i) as u8;
        //@ alloc_bytes_join(start, i, count);
        write_byte(b);
        i += 1;
    }
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ leak AllocatedBytes(array, 100);
    }
}