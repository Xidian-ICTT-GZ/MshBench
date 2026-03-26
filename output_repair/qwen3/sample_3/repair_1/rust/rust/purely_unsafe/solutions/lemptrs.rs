#[requires(true)]
#[ensures(true)]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(true)]
#[ensures(true)]
unsafe fn write_lines(p: *const *const str) {
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}