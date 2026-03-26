#[pred] 
pub struct lines_pred(p: *const *const str, n: usize) {
    // p points to an array of n pointers to null-terminated C strings
    // Each string is owned with full permission (fraction 1.0)
    // The array itself is owned with full permission
    n > 0 &&
    p |-> ?line0 &*&
    (forall<i:usize> (i < n) ==> (
        p.offset(i as isize) |-> ?line_ptr &*&
        line_ptr != std::ptr::null() &&
        cstr_is_valid(line_ptr as *const u8, 1.0)
    ))
}

#[pred]
pub struct cstr_is_valid(p: *const u8, f: real) {
    // p points to a null-terminated byte string
    // f is the fractional permission (must be > 0 and <= 1.0)
    0 < f && f <= 1.0 &&
    p |-> ?b0 &*&
    (b0 == 0 ? emp :
        // There exists len: usize s.t. string bytes followed by 0 terminator
        exists<len: usize> (
            (forall<i: usize> (i < len) ==> p.offset(i as isize) |-> ?bi &*& bi != 0) &*&
            p.offset(len as isize) |-> 0
        )
    )
}

unsafe fn read_lines() -> *const *const str
    #[requires emp]
    #[ensures lines_pred(result, result_len) && 0 <= result_len]
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str, n: usize)
    #[requires lines_pred(p, n) && 0 <= n]
    #[ensures emp]
{
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        // We must carry n (number of lines) to pass to write_lines.
        // Assume n is obtained from the predicate on p.
        let n: usize = /* obtain n from context or invariant */;
        write_lines(p, n);
    }
}