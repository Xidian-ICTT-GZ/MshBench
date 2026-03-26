use verifast::prelude::*;

predicate lines(p: *const *const str) = (*p) |-> ?s &*& s as *const str == p.offset(1) &*& true;

#[requires(true)]
#[ensures(lines(result))]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(lines(p))]
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