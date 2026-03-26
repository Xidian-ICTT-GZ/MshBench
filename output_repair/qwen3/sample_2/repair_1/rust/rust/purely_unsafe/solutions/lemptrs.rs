#[predicate]
fn lines_ptr(p: *const *const str) = (*p) |-> _;

unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(lines_ptr(p))]
unsafe fn write_lines(p: *const *const str) {
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();
        write_lines(p);
    }
}