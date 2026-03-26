predicate lines_data(p: *const *const str;) =
    pointer(p, _) &*&
    pointer(*p, _);

#[ensures(lines_data(result))]
unsafe fn read_lines() -> *const *const str
    //@ requires true;
    //@ ensures lines_data(result);
{
    std::process::abort();
}

#[requires(lines_data(p))]
unsafe fn write_lines(p: *const *const str)
    //@ requires lines_data(p);
    //@ ensures lines_data(p);
{
    std::process::abort();
}

fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}