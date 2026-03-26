predicate lines_data(p: *const *const str) = 
    p->?line_ptr &*&
    line_ptr != 0 ? str_slice(line_ptr, _) : false;

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