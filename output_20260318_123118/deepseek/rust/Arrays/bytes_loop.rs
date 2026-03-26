use std::io::{Read, Write, stdin, stdout};

#[predicate]
fn u8_slice(ptr: *mut u8, count: usize) -> bool {
    exists!{|i: usize| 0 <= i && i <= count && 
        forall(|k: usize| 0 <= k && k < i ==> u8::inv(*(ptr.add(k)))) &&
        forall(|k: usize| i <= k && k < count ==> *ptr.add(k) == 0u8)}
}

#[predicate]
fn u8_slice_full(ptr: *mut u8, count: usize) -> bool {
    forall(|k: usize| 0 <= k && k < count ==> u8::inv(*(ptr.add(k))))
}

unsafe fn read_byte() -> u8
#[requires(stdin()@StdIn)]
#[ensures(|result| u8::inv(result) && stdin()@StdIn)]
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
#[requires(u8::inv(value) && stdout()@StdOut)]
#[ensures(stdout()@StdOut)]
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
#[requires(0 < count)]
#[ensures(|result| !result.is_null() && u8_slice(result, count))]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
#[requires(u8_slice(start, count))]
#[ensures(u8_slice_full(start, count))]
{
    let mut i = 0;
    #[invariant(0 <= i && i <= count)]
    #[invariant(u8_slice(start, count))]
    #[invariant(forall(|k: usize| 0 <= k && k < i ==> u8::inv(*(start.add(k)))))]
    loop {
        if i == count { break; }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
#[requires(u8_slice_full(start, count))]
#[ensures(u8_slice_full(start, count))]
{
    let mut i = 0;
    #[invariant(0 <= i && i <= count)]
    #[invariant(u8_slice_full(start, count))]
    #[invariant(forall(|k: usize| 0 <= k && k < i ==> u8::inv(*(start.add(k)))))]
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