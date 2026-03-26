use std::io::{Read, Write, stdin, stdout};

/*@
predicate alloc_block_io(usize count) = true;
@*/

unsafe fn read_byte() -> u8
//@ req alloc_block_io(1);
//@ ens alloc_block_io(1);
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ req alloc_block_io(1);
//@ ens alloc_block_io(1);
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

/*@
predicate alloc_block(usize count, *mut u8 ptr) =
    ptr != 0 &*& malloc_block(ptr, count) &*& u8s(ptr, count, _);
@*/

unsafe fn alloc(count: usize) -> *mut u8
//@ req count > 0;
//@ ens alloc_block(count, result);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req alloc_block(count, start) &*& alloc_block_io(count);
//@ ens alloc_block(count, start) &*& alloc_block_io(count);
{
    let mut i = 0;
    loop {
        //@ inv 0 <= i && i <= count &*& alloc_block(count, start) &*& alloc_block_io(count - i);
        //@ open alloc_block(count, start);
        //@ open u8s(start, count, _);
        //@ close u8s(start, count, _);
        //@ close alloc_block(count, start);
        
        if i == count {
            //@ close alloc_block(count, start);
            break;
        }
        let b = read_byte();
        //@ open alloc_block(count, start);
        //@ open u8s(start, count, ?contents);
        //@ u8s_split(start, i);
        *start.add(i) = b;
        //@ u8s_join(start);
        //@ close u8s(start, count, _);
        //@ close alloc_block(count, start);
        i += 1;
        //@ open alloc_block_io(count - i + 1);
        //@ close alloc_block_io(count - i);
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req alloc_block(count, start) &*& alloc_block_io(count);
//@ ens alloc_block(count, start) &*& alloc_block_io(count);
{
    let mut i = 0;
    loop {
        //@ inv 0 <= i && i <= count &*& alloc_block(count, start) &*& alloc_block_io(count - i);
        //@ open alloc_block(count, start);
        //@ open u8s(start, count, _);
        //@ close u8s(start, count, _);
        //@ close alloc_block(count, start);
        
        if i == count { 
            //@ close alloc_block(count, start);
            break; 
        }
        //@ open alloc_block(count, start);
        //@ open u8s(start, count, ?contents);
        //@ u8s_split(start, i);
        write_byte(*start.add(i));
        //@ u8s_join(start);
        //@ close u8s(start, count, contents);
        //@ close alloc_block(count, start);
        i += 1;
        //@ open alloc_block_io(count - i + 1);
        //@ close alloc_block_io(count - i);
    }
}

fn main() {
    unsafe {
        //@ close alloc_block_io(100);
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        //@ open alloc_block(100, array);
        //@ open u8s(array, 100, _);
        //@ leak malloc_block(array, 100);
        //@ open alloc_block_io(0);
    }
}