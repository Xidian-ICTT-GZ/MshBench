//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let text = alloc(10);
        //@ close u8_slice(text, 10, _);
        let key = alloc(10);
        //@ close u8_slice(key, 10, _);
        read_bytes(text, 10);
        read_bytes(key, 10);
        xor_bytes(text, key, 10);
        write_bytes(text, 10);
    }
}

/*@ pred u8_slice(ptr: *mut u8, len: usize, vs: list<u8>) =
    if len == 0 then ptr == 0 &*& vs == nil
    else alloc_block_(ptr as *u8, len) &*& vs == cons(?v, ?vs0) &*& [_](*ptr |-> v) &*& u8_slice(ptr + 1, len - 1, vs0);
@*/

//@ req true;
//@ ens u8_slice(result, count, _);
unsafe fn alloc(count: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    //@ close u8_slice(result, count, repeat(0, count));
    result
}

//@ req u8_slice(start, count, ?vs);
//@ ens u8_slice(start, count, ?ws);
unsafe fn read_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        //@ open u8_slice(start, count, vs);
        let b = read_byte();
        *start = b;
        //@ close u8_slice(start, 1, cons(b, nil));
        read_bytes(start.add(1), count - 1);
        //@ open u8_slice(start + 1, count - 1, _);
        //@ close u8_slice(start, count, cons(b, _));
    } else {
        //@ close u8_slice(start, 0, nil);
    }
}

//@ req u8_slice(text, count, ?text_vs) &*& u8_slice(key, count, ?key_vs);
//@ ens u8_slice(text, count, ?result_vs) &*& u8_slice(key, count, key_vs);
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
    if count > 0 {
        //@ open u8_slice(text, count, text_vs);
        //@ open u8_slice(key, count, key_vs);
        let t = *text;
        let k = *key;
        *text = t ^ k;
        //@ close u8_slice(text, 1, cons(t ^ k, nil));
        xor_bytes(text.add(1), key.add(1), count - 1);
        //@ open u8_slice(text + 1, count - 1, _);
        //@ open u8_slice(key + 1, count - 1, _);
        //@ close u8_slice(text, count, cons(t ^ k, _));
        //@ close u8_slice(key, count, key_vs);
    } else {
        //@ close u8_slice(text, 0, nil);
        //@ close u8_slice(key, 0, nil);
    }
}

//@ req u8_slice(start, count, ?vs);
//@ ens u8_slice(start, count, vs);
unsafe fn write_bytes(start: *mut u8, count: usize) {
    if count > 0 {
        //@ open u8_slice(start, count, vs);
        let b = *start;
        write_byte(b);
        //@ close u8_slice(start, 1, cons(b, nil));
        write_bytes(start.add(1), count - 1);
        //@ open u8_slice(start + 1, count - 1, _);
        //@ close u8_slice(start, count, vs);
    } else {
        //@ close u8_slice(start, 0, nil);
    }
}

//@ req true;
//@ ens true;
unsafe fn read_byte() -> u8 {
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

//@ req true;
//@ ens true;
unsafe fn write_byte(value: u8) {
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}