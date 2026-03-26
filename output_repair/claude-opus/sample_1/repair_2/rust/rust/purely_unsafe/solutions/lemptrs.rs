unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

unsafe fn write_lines(_p: *const *const str) {
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}