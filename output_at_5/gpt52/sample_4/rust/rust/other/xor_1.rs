use std::io::{Read, Write, stdin, stdout};
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
//@ ens true;
{
let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
let result = std::alloc::alloc(layout);
if result.is_null() {
std::alloc::handle_alloc_error(layout);
}
result
}
unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req true;
//@ ens true;
{
let mut i: usize = 0;
while i < count
//@ inv true;
{
let b = read_byte();
*start.add(i) = b;
i += 1;
}
}
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
//@ req true;
//@ ens true;
{
let mut i: usize = 0;
while i < count
//@ inv true;
{
let t = *text.add(i);
let k = *key.add(i);
*text.add(i) = t ^ k;
i += 1;
}
}
unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req true;
//@ ens true;
{
let mut i: usize = 0;
while i < count
//@ inv true;
{
let b = *start.add(i);
write_byte(b);
i += 1;
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

}
}