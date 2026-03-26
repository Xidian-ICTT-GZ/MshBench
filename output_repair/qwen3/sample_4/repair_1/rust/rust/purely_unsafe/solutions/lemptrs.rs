#[predicate]
fn lines_resource(p: *const *const str) = (*p) |-> ?s &*& string(s);

unsafe fn read_lines() -> *const *const str
    requires true;
    ensures lines_resource(result);
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str)
    requires lines_resource(p);
    ensures true;
{
    std::process::abort();
}

fn main()
    requires true;
    ensures true;
{
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}