#[pred] 
pub struct lines_pred(p: *const *const str, n: usize) {
    // p points to an array of n pointers to null-terminated C strings
    // Each string is owned with full permission (fraction 1.0)
    // The array itself is owned with full permission
    exists!(i: usize; i < n) => 
        p.offset(i as isize) |-> ?line_ptr &&
        line_ptr != 0 &&
        *line_ptr |-> ?cstr &&
        cstr_is_valid(cstr, 1.0)
}

#[pred]
pub struct cstr_is_valid(p: *const u8, f: real) {
    // p points to a null-terminated byte string
    // f is the fractional permission (must be > 0 and <= 1.0)
    f > 0 && f <= 1.0 &&
    exists!(len: usize; 
        p |-> ?b0 &&
        b0 == 0 => len == 0,
        b0 != 0 => (
            p.offset(0 as isize) |-> b0 &&
            exists!(i: usize; i < len) =>
                p.offset((i+1) as isize) |-> ?bi &&
                bi != 0 ||
                (i == len - 1 && bi == 0)
        )
    )
}

unsafe fn read_lines() -> *const *const str {
    #[requires true]
    #[ensures lines_pred(result, ?n) && n >= 0]
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str) {
    #[requires lines_pred(p, n) && n >= 0]
    #[ensures true]
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}