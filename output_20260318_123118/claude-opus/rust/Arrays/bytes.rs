use std::io::{Read, Write, stdin, stdout};

predicate byte_cell(predicate(char)) (byte*);

predicate array_bytes(void* start, usize count, list<u8> vs) =
  count == 0 ?
    emp
  :
    exists<u8, void*> (v, next) &*&
      start |-> v &*&
      array_bytes(next, count - 1, tail(vs)) &*&
      next == (start as usize + 1) as void* &*&
      head(vs) == v;

#[requires(true)]
#[ensures(result != 0)]
unsafe fn alloc(count: usize) -> *mut u8
  //@ requires true;
  //@ ensures array_bytes(result, count, ?vs);
{
    let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
    let result = std::alloc::alloc(layout);
    if result.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    result
}

#[requires(array_bytes(start, count, ?vs))]
#[ensures(array_bytes(start, count, vs))]
unsafe fn read_bytes(start: *mut u8, count: usize)
  //@ requires array_bytes(start, count, _);
  //@ ensures array_bytes(start, count, _);
{
    if count > 0 {
        let b = read_byte();
        *start = b;
        read_bytes(start.add(1), count - 1);
    }
}

#[requires(array_bytes(start, count, ?vs))]
#[ensures(array_bytes(start, count, vs))]
unsafe fn write_bytes(start: *mut u8, count: usize)
  //@ requires array_bytes(start, count, ?vs);
  //@ ensures array_bytes(start, count, vs);
{
    if count > 0 {
        let b = *start;
        write_byte(b);
        write_bytes(start.add(1), count - 1);
    }
}

#[requires(true)]
#[ensures(true)]
unsafe fn read_byte() -> u8
  //@ requires true;
  //@ ensures true;
{
    let mut buf = [0u8];
    stdin().read_exact(&mut buf[..]).unwrap();
    buf[0]
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_byte(value: u8)
  //@ requires true;
  //@ ensures true;
{
    let buf = [value];
    stdout().write(&buf[..]).unwrap();
}

fn main()
  //@ requires true;
  //@ ensures true;
{
    unsafe {
        let array = alloc(100);
        read_bytes(array, 100);
        write_bytes(array, 100);
        write_bytes(array, 100);
    }
}