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
//@ req count as int >= 0;
//@ ens [_]alloc_block(result, count as int);
{
let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
let result = std::alloc::alloc(layout);
if result.is_null() {
std::alloc::handle_alloc_error(layout);
}
result
}
unsafe fn read_bytes(start: *mut u8, count: usize)
//@ req [_]alloc_block(start, count as int);
//@ ens [_]alloc_block(start, count as int);
{
if count > 0 {
//@ open [_]alloc_block(start, count as int);
let b = read_byte();
*start = b;
//@ close [_]alloc_block(start, 1);
//@ close [_]alloc_block(start.add(1), count as int - 1);
read_bytes(start.add(1), count - 1);
//@ open [_]alloc_block(start.add(1), count as int - 1);
//@ close [_]alloc_block(start, count as int);
} else {
//@ open [_]alloc_block(start, 0);
//@ close [_]alloc_block(start, 0);
}
}
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize)
//@ req [_]alloc_block(text, count as int) &*& [_]alloc_block(key, count as int);
//@ ens [_]alloc_block(text, count as int) &*& [_]alloc_block(key, count as int);
{
if count > 0 {
//@ open [_]alloc_block(text, count as int);
//@ open [_]alloc_block(key, count as int);
let t = *text;
let k = *key;
*text = t ^ k;
//@ close [_]alloc_block(text, 1);
//@ close [_]alloc_block(key, 1);
//@ close [_]alloc_block(text.add(1), count as int - 1);
//@ close [_]alloc_block(key.add(1), count as int - 1);
xor_bytes(text.add(1), key.add(1), count - 1);
//@ open [_]alloc_block(text.add(1), count as int - 1);
//@ open [_]alloc_block(key.add(1), count as int - 1);
//@ close [_]alloc_block(text, count as int);
//@ close [_]alloc_block(key, count as int);
} else {
//@ open [_]alloc_block(text, 0);
//@ close [_]alloc_block(text, 0);
//@ open [_]alloc_block(key, 0);
//@ close [_]alloc_block(key, 0);
}
}
unsafe fn write_bytes(start: *mut u8, count: usize)
//@ req [_]alloc_block(start, count as int);
//@ ens [_]alloc_block(start, count as int);
{
if count > 0 {
//@ open [_]alloc_block(start, count as int);
let b = *start;
write_byte(b);
//@ close [_]alloc_block(start, 1);
//@ close [_]alloc_block(start.add(1), count as int - 1);
write_bytes(start.add(1), count - 1);
//@ open [_]alloc_block(start.add(1), count as int - 1);
//@ close [_]alloc_block(start, count as int);
} else {
//@ open [_]alloc_block(start, 0);
//@ close [_]alloc_block(start, 0);
}
}
fn main()
//@ req true;
//@ ens true;
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