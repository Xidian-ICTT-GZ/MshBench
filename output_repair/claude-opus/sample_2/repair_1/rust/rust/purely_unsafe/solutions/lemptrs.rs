unsafe fn read_lines() -> *const *const str
//@ req true;
//@ ens true;
{
    std::process::abort();
}

unsafe fn write_lines(p: *const *const str)
//@ req true;
//@ ens true;
{
    std::process::abort();
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let p = read_lines();

        write_lines(p);
    }
}