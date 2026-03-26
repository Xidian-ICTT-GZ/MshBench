#[pred] 
pub struct cstr_is_valid(p: *const u8, f: real) {
    f > 0 && f <= 1.0 &&
    exists!(len: nat; // len = length of string excluding null terminator
        // owns the first byte
        p |-> ?b0 &&
        (
            b0 == 0 ? len == 0 &&
                      // single null terminator byte owned
                      true
            :
            (
                // owns bytes p[0..len], with last byte not null
                (forall(i: nat) :: i < len ==> 
                    p.offset(i as isize) |-> ?bi && bi != 0) &&
                // owns the null terminator byte at p[len]
                p.offset(len as isize) |-> 0
            )
        )
    )
}

#[pred]
pub struct lines_pred(p: *const *const u8, n: nat) {
    n >= 0 &&
    n == 0 ? p |-> _ // owns the pointer to zero-length array (dummy) or just empty ownership
    :
    (
        p |-> ?line_ptr &*&
        line_ptr != null as *const u8 &*&
        cstr_is_valid(line_ptr, 1.0) &*&
        lines_pred(p.offset(1), n - 1)
    )
}

unsafe fn read_lines() -> *const *const u8
    #[requires true]
    #[ensures lines_pred(result, ?n)]
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const u8)
    #[requires exists(n: nat) &*& lines_pred(p, n)]
    #[ensures true]
{
    std::process::abort();
}

fn main() {
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}