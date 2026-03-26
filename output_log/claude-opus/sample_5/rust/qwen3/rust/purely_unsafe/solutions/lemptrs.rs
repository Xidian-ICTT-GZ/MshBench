#[pred]
pub struct cstr_is_valid(p: *const u8, f: real)
  = 0 < f &*& f <= 1.0 &*&
    p |-> ?b0 &*&
    (b0 == 0 ?
       emp
     :
       exists!(len: nat, bs: list<u8>) &*&
         cstring_chars(p, bs, len) &*&
         length(bs) == len &*&
         (nth(bs, len - 1) == 0));

#[pred]
pub cstring_chars(p: *const u8, bs: list<u8>, len: nat)
  = len == 0 ?
      emp
    :
      p |-> head(bs) &*& cstring_chars(p.offset(1), tail(bs), len - 1);

#[pred]
pub struct lines_pred(p: *const *const u8, n: usize)
  = n == 0 ?
      emp
    :
      p |-> ?line_ptr &*&
      cstr_is_valid(line_ptr, 1.0) &*&
      lines_pred(p.offset(1), n - 1);

unsafe fn read_lines()
  #[requires true]
  #[ensures lines_pred(result, ?n) &*& n >= 0]
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const u8)
  #[requires exists!(n: usize) lines_pred(p, n) &*& n >= 0]
  #[ensures true]
{
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}