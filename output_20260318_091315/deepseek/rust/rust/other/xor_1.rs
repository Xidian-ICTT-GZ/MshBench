use std::io::{Read, Write, stdin, stdout};

/*@
predicate_ctor array8_slice(*start: *mut u8, count: usize)() = 
    count == 0 ? true : 
    integer(start, ?v) &*& array8_slice(start.offset(1), count - 1)();

predicate array8(*start: *mut u8, count: usize) = 
    count == 0 ? true : 
    malloc_block(start, 1) &*& integer(start, ?v) &*& array8(start.offset(1), count - 1);

lemma void split_array8(*start: *mut u8, count: usize, i: usize)
    requires array8(start, count) &*& 0 <= i &*& i <= count;
    ensures array8(start, i) &*& array8(start.offset(i), count - i);
{
    open array8(start, count);
    if (count == 0) {
    } else {
        if (i == 0) {
            close array8(start, 0);
        } else {
            split_array8(start.offset(1), count - 1, i - 1);
            close array8(start, i);
        }
    }
}

lemma void merge_array8(*start: *mut u8, i: usize, count: usize)
    requires array8(start, i) &*& array8(start.offset(i), count - i);
    ensures array8(start, count);
{
    open array8(start, i);
    if (i == 0) {
    } else {
        merge_array8(start.offset(1), i - 1, count - 1);
        close array8(start, count);
    }
}
@*/

#[requires(count > 0)]
#[ensures(result == 0 || result == 1)]
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(value >= 0 && value <= 255)]
#[ensures(true)]
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

#[requires(count > 0)]
#[ensures(array8(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close array8(result, count);
    result
}

#[requires(array8(start, count))]
#[ensures(array8(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        //@ split_array8(start, count, 1);
        //@ open array8(start, 1);
        let b = read_byte();
        *start = b;
        //@ close array8(start, 1);
        read_bytes(start.add(1), count - 1);
        //@ merge_array8(start, 1, count);
    } else {
        //@ close array8(start, 0);
    }
}

#[requires(array8(text, count) &*& array8(key, count))]
#[ensures(array8(text, count) &*& array8(key, count))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
{
    if count > 0 {
        //@ split_array8(text, count, 1);
        //@ split_array8(key, count, 1);
        //@ open array8(text, 1);
        //@ open array8(key, 1);
        let t = *text;
        let k = *key;
        *text = t ^ k;
        //@ close array8(text, 1);
        //@ close array8(key, 1);
        xor_bytes(text.add(1), key.add(1), count - 1);
        //@ merge_array8(text, 1, count);
        //@ merge_array8(key, 1, count);
    } else {
        //@ close array8(text, 0);
        //@ close array8(key, 0);
    }
}

#[requires(array8(start, count))]
#[ensures(array8(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    if count > 0 {
        //@ split_array8(start, count, 1);
        //@ open array8(start, 1);
        let b = *start;
        write_byte(b);
        //@ close array8(start, 1);
        write_bytes(start.add(1), count - 1);
        //@ merge_array8(start, 1, count);
    } else {
        //@ close array8(start, 0);
    }
}

fn main()
{
    unsafe {
        let text = alloc(10);
        let key = alloc(10);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
        //@ leak array8(text, 10) &*& array8(key, 10);
    }
}