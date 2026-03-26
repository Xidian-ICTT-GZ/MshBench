#[pred]
pub struct cstr_is_valid(p: *const u8, f: real) {
    // p points to a null-terminated byte string with fractional permission f (0 < f <= 1)
    f > 0 && f <= 1.0 &&
    exists!(len: usize;
        len >= 0 &&
        // Permission to read bytes p[0..=len]
        chars_slice(p, len + 1, f) &&
        // The last byte (p[len]) is zero
        p.offset(len as isize) |-> ?last_char &&
        last_char == 0 &&
        // All bytes before 'len' are non-zero
        forall_chars_nonzero(p, len)
    )
}

#[predicate]
fn chars_slice(p: *const u8, len: usize, f: real) = 
    len == 0 ? emp : 
    p |-> ?b &*& chars_slice(p.offset(1), len - 1, f);

#[predicate]
fn forall_chars_nonzero(p: *const u8, len: usize) =
    len == 0 ? emp :
    (p |-> ?b &*& b != 0) &*& forall_chars_nonzero(p.offset(1), len - 1);

#[pred]
pub struct lines_pred(p: *const *const u8, n: usize) {
    n > 0 ?
        p |-> ?line_ptr &*&
        line_ptr != 0 &*&
        cstr_is_valid(line_ptr, 1.0) &*&
        lines_pred(p.offset(1), n - 1)
    : emp
}

unsafe fn read_lines() -> *const *const u8 
    #[requires true]
    #[ensures lines_pred(result, ?n)]
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const u8) 
    #[requires lines_pred(p, ?n)]
    #[ensures emp]
{
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}