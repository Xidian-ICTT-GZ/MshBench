fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let mut x = 0;
        let mut y = 0;

        //@ open_full_borrow_content::<i32>(&x);
        //@ close_full_borrow_content::<i32>(&x);
        //@ open_full_borrow_content::<i32>(&y);
        //@ close_full_borrow_content::<i32>(&y);

        //@ requires false;
        std::hint::unreachable_unchecked();
    }
}