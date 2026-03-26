predicate lines_data(p: *const *const str;) =
    pointer(p, _);

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