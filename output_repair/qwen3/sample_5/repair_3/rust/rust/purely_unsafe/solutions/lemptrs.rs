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
fn lines_resource(p: *const *const str, s: *const str) = (*p) |-> s &*& string_slice(s);

#[requires(true)]
#[ensures(exists(s: *const str, lines_resource(result, s)))]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(exists(s: *const str, lines_resource(p, s)))]
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