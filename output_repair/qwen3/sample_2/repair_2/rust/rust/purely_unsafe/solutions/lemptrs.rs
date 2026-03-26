unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str) {
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}

#[predicate]
fn lines_ptr(p: *const *const str) = (*p) |-> ?s &*& [_]std::string::str_points_to(s);

#[requires(lines_ptr(p))]
#[ensures(true)]
unsafe fn write_lines(p: *const *const str) {
    std::process::abort();
}

#[ensures(lines_ptr(result))]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}