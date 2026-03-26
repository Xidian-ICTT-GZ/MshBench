unsafe fn read_lines() -> *const *const str
//@ requires true;
//@ ensures result == 0;
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str)
//@ requires p == 0;
//@ ensures true;
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