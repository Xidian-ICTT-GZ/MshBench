#[predicate]
fn lines_token(p: *const *const str) = (*p) |-> _;

unsafe fn read_lines() -> *const *const str
    requires true,
    ensures lines_token(result),
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str)
    requires lines_token(p),
    ensures true,
{
    std::process::abort();
}

fn main()
    requires true,
    ensures true,
{
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}