use std::io::{Read, Write, stdin, stdout};

/*@ pred block(start: *mut u8, count: usize; bytes: list<u8>) =
    if count == 0 then start == 0 as *mut u8 &*& bytes == nil
    else alloc_block(start, count) &*& u8_slice(start, count, ?bs) &*& bytes == bs;
@*/

unsafe fn read_byte() -> u8
//@ req true;
//@ ens true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
//@ req true;
//@ ens true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
//@ req true;
//@ ens count == 0 ? result == 0 as *mut u8 : block(result, count, _);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ if count > 0 { close block(result, count, _); }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req block(start, count, _);
//@ ens block(start, count, _);
{
    
    if count > 0 {
        //@ open block(start, count, _);
        let b = read_byte();
        *start = b;
        //@ close u8_slice(start, 1, [b]);
        read_bytes(start.add(1), count - 1);
        //@ close block(start, count, _);
    }
    
}

unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req block(start, count, _);
//@ ens block(start, count, _);
{
    if count > 0 {
        
        //@ open block(start, count, _);
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
        //@ close block(start, count, _);
        
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
        
    }
}