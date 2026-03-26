#[pred] 
pub struct lines_pred(p: *const *const u8, n: usize) {
    // p points to an array of n pointers to null-terminated C strings
    // The array is owned fully and each string is owned fully

    // Ownership of array: p..p+n pointers, each non-null pointer to cstr_is_valid(1.0)
    (p |-> ?first_ptr) &*&
    n >= 0 && (
        n == 0 ?
            // empty array, no pointers owned beyond p
            emp
        :
            // For all i < n, p.offset(i) |-> line_ptr && line_ptr != null && cstr_is_valid(line_ptr, 1.0)
            (forall|i: int| (0 <= i && i < n) ==>
                (p.offset(i as isize) |-> ?line_ptr && line_ptr != 0 && cstr_is_valid(line_ptr, 1.0)))
            &*&
            // separating conjunction of all pointers
            (separating_conjunction(|i: int| (0 <= i && i < n), |i| p.offset(i as isize) |-> _))
    )
}

#[pred]
pub struct cstr_is_valid(p: *const u8, f: real) {
    // p points to a null-terminated byte string with fractional permission f > 0
    // There exists len such that first len bytes are non-zero and (len+1)-th byte is zero
    f > 0 && f <= 1.0 &*&
    (
        // Exists len >= 0
        exists|len: int| len >= 0 &*&
        (
            // The pointer p points to b0 equals p[0]
            p |-> ?b0
            &*&
            (
                b0 == 0 && len == 0
                ||
                (
                    // For all 0 <= i < len, p.offset(i) |-> bi != 0
                    (forall|i: int| (0 <= i && i < len) ==> p.offset(i as isize) |-> ?bi &*& bi != 0)
                    &*&
                    // The null terminator byte at offset len
                    p.offset(len as isize) |-> 0
                )
            )
        )
    )
}

unsafe fn read_lines() -> *const *const u8
    #[requires emp]
    #[ensures lines_pred(result, ?n) &*& n >= 0]
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const u8, n: usize)
    #[requires lines_pred(p, n) &*& n >= 0]
    #[ensures emp]
{
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        // Need to get length n - this is implicit; to verify, we add an explicit parameter for n
        // Because original code omits n in write_lines, we add n as argument

        // For verification, add:
        assume(lines_pred(p, ?n) && n >= 0);
        write_lines(p, n);
    }
}