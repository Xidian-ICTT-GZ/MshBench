predicate lines_data(p: *const *const str;) =
    p != std::ptr::null() &*&
    pointer(p, ?first) &*&
    first != std::ptr::null() &*&
    pointer(first, _) &*&
    // For demonstration assume the array is null-terminated pointer array
    // owning each string pointer and each string pointer owns a string
    // Here we approximate by owning a non-null pointer to a valid string.
    // In practice, use a recursive predicate or an explicit length.
    // This minimal predicate grants ownership of p and of first element.

#[ensures(lines_data(result))]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(lines_data(p))]
unsafe fn write_lines(p: *const *const str) {
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}