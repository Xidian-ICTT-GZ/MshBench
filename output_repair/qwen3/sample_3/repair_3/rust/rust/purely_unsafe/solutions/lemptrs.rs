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


use verifast::prelude::*;

predicate lines(p: *const *const str; count: nat) =
    match count {
        0 => p == null(),
        _ => (*p) |-> ?s &*& s as *const str == p.offset(1) &*& lines(p.offset(1), count - 1)
    };

#[requires(true)]
#[ensures(exists<count> lines(result, count))]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(exists<count> lines(p, count))]
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