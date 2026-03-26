#[predicate]
fn lines_resource(p: *const *const str) = (*p) |-> ?s &*& string_slice(s);

unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(lines_resource(p))]
#[ensures(true)]
unsafe fn write_lines(p: *const *const str) {
    std::process::abort();
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let p = read_lines();
        write_lines(p);
    }
}