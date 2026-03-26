predicate str_slice_slice(s: *const str, len: nat) = pointer(s, _);

predicate line_data(line: *const str) = pointer(line, _);

predicate lines_data(p: *const *const str, n: nat) =
    p |-> ?arr &*& array_lines(arr, n);

predicate array_lines(arr: *const *const str, n: nat) =
    (n == 0 ?
        true
        : arr |-> ?line_ptr &*& line_data(line_ptr) &*&
          array_lines(arr.offset(1), n - 1)
    );

#[requires(true)]
#[ensures(lines_data(result, ?n))]
unsafe fn read_lines() -> *const *const str {
    std::process::abort();
}

#[requires(lines_data(p, ?n))]
#[ensures(lines_data(p, n))]
unsafe fn write_lines(p: *const *const str) {
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}