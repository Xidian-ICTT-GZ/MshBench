use std::io::{Read, Write, stdin, stdout};

#[predicate]
fn u8_slice(ptr: *mut u8, len: usize) -> bool {
    exists!{|i: usize| i <= len && 
        forall(|j: usize| 0 <= j && j < i ==> u8::inv(*(ptr.add(j)))) &&
        (i == len ==> true) &&
        (i < len ==> exists!{|v: u8| *(ptr.add(i)) |-> v && u8_slice(ptr.add(i+1), len - i - 1)})}
}

#[predicate]
fn full_u8_slice(ptr: *mut u8, len: usize) -> bool {
    exists!{|i: usize| i <= len && 
        forall(|j: usize| 0 <= j && j < i ==> exists!{|v: u8| *(ptr.add(j)) |-> v}) &&
        (i == len ==> true) &&
        (i < len ==> *(ptr.add(i)) |-> _ && full_u8_slice(ptr.add(i+1), len - i - 1))}
}

#[predicate]
fn alloc_layout(count: usize) -> bool {
    count <= usize::MAX
}

unsafe fn read_byte() -> u8
#[requires(true)]
#[ensures(result <= 255)]
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

unsafe fn write_byte(value: u8)
#[requires(value <= 255)]
#[ensures(true)]
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

unsafe fn alloc(count: usize) -> *mut u8
#[requires(alloc_layout(count))]
#[ensures(result != 0 as *mut u8 && full_u8_slice(result, count))]
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

unsafe fn read_bytes(start: *mut u8, count: usize)
#[requires(full_u8_slice(start, count))]
#[ensures(full_u8_slice(start, count))]
{
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(full_u8_slice(start.add(i), count - i))]
    #[invariant(exists!{|j: usize| j <= i && forall(|k: usize| 0 <= k && k < j ==> exists!{|v: u8| *(start.add(k)) |-> v})})]
    loop {
        if i == count { break; }
        let b = read_byte();
        *(start.add(i)) = b;
        i += 1;
    }
}

unsafe fn write_bytes(start: *mut u8, count: usize)
#[requires(full_u8_slice(start, count))]
#[ensures(full_u8_slice(start, count))]
{
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(full_u8_slice(start.add(i), count - i))]
    #[invariant(exists!{|j: usize| j <= i && forall(|k: usize| 0 <= k && k < j ==> exists!{|v: u8| *(start.add(k)) |-> v})})]
    loop {
        if i == count { break; }
        let b = *(start.add(i));
        write_byte(b);
        i += 1;
    }
}

fn main()
#[requires(true)]
#[ensures(true)]
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}