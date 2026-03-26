use std::io::{Read, Write, stdin, stdout};

#[predicate]
fn u8_slice(ptr: *mut u8, count: usize) -> bool {
    exists!{|i: usize| 0 <= i && i <= count &&
        forall(|j: usize| 0 <= j && j < i ==> exists!{|v: u8| ptr.add(j)@v}) &&
        forall(|j: usize| i <= j && j < count ==> exists!{|v: u8| ptr.add(j)@v})}
}

#[predicate]
fn u8_slice_full(ptr: *mut u8, count: usize) -> bool {
    forall(|j: usize| 0 <= j && j < count ==> exists!{|v: u8| ptr.add(j)@v})
}

#[predicate]
fn alloc_layout(count: usize) -> bool {
    count <= usize::MAX
}

#[requires(alloc_layout(count))]
#[ensures(result != 0 as *mut u8 ==> u8_slice(result, count))]
unsafe fn alloc(count: usize) -> *mut u8
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(u8_slice(start, count))]
#[ensures(u8_slice_full(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(u8_slice(start, count))]
    #[invariant(forall(|j: usize| 0 <= j && j < i ==> exists!{|v: u8| start.add(j)@v}))]
    loop {
        if i == count {
            break;
        }
        let b = read_byte();
        *start.add(i) = b;
        i += 1;
    }
}

#[requires(u8_slice_full(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize)
{
    let mut i = 0;
    #[invariant(i <= count)]
    #[invariant(u8_slice_full(start, count))]
    #[invariant(forall(|j: usize| 0 <= j && j < i ==> exists!{|v: u8| start.add(j)@v}))]
    loop {
        if i == count { break; }
        write_byte(*start.add(i));
        i += 1;
    }
}

#[ensures(true)]
unsafe fn read_byte() -> u8
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
unsafe fn write_byte(value: u8)
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

fn main() {
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}