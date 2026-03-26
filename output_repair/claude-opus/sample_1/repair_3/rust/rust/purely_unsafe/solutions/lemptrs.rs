predicate lines_ptr(p: *const *const str) = true;

#[requires(true)]
#[ensures(lines_ptr(result))]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(lines_ptr(p))]
#[ensures(true)]
unsafe fn write_lines(_p: *const *const str) {
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}