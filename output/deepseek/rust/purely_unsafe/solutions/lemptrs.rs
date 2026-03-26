unsafe fn read_lines() -> *const *const str {
    #[requires(true)]
    #[ensures(result.is_null() ? true : *result |-> _)]
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str) {
    #[requires(!p.is_null() ==> *p |-> _)]
    #[ensures(true)]
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}