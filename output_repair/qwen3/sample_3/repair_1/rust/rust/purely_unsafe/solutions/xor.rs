use std::io::{stdin, stdout, Read, Write};

predicate bytes_owned(ptr: *mut u8, len: usize) =
  ptr != null_mut() && len > 0;

predicate bytes_content(ptr: *mut u8, len: usize, val: [u8]) =
  ptr != null_mut() && len == val.len() && {
    let mut i = 0usize;
    while i < len {
      *ptr.add(i) == val[i];
      i += 1;
    }
    true
  };

#[requires(bytes_owned(start, count))]
#[ensures(bytes_owned(start, count))]
unsafe fn read_bytes(start: *mut u8, count: usize) {
  if count > 0 {
    let b: u8 = {
      let mut buf = [0u8];
      stdin().read_exact(&mut buf[..]).unwrap();
      buf[0]
    };
    *start = b;
    read_bytes(start.add(1), count - 1);
  }
}

#[requires(bytes_owned(text, count) && bytes_owned(key, count))]
#[ensures(bytes_owned(text, count) && bytes_owned(key, count))]
unsafe fn xor_bytes(text: *mut u8, key: *mut u8, count: usize) {
  if count > 0 {
    let t = *text;
    let k = *key;
    *text = t ^ k;
    xor_bytes(text.add(1), key.add(1), count - 1);
  }
}

#[requires(bytes_owned(start, count))]
#[ensures(bytes_owned(start, count))]
unsafe fn write_bytes(start: *mut u8, count: usize) {
  if count > 0 {
    let b = *start;
    let buf = [b];
    stdout().write(&buf[..]).unwrap();
    write_bytes(start.add(1), count - 1);
  }
}

#[ensures(bytes_owned(result, count) && count > 0)]
unsafe fn alloc(count: usize) -> *mut u8 {
  let layout = std::alloc::Layout::from_size_align(count, 1).unwrap();
  let result = std::alloc::alloc(layout);
  if result.is_null() {
    std::alloc::handle_alloc_error(layout);
  }
  result
}

fn main() {
  unsafe {
    let text = alloc(10);
    let key = alloc(10);
    read_bytes(text, 10);
    read_bytes(key, 10);
    xor_bytes(text, key, 10);
    write_bytes(text, 10);
  }
}