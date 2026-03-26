use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
impl Account {
    /*
    //@ pred account_pointer(Account *p; int balance) = p->balance |-> balance;
    */
    unsafe fn create() -> *mut Account
        //@ requires true;
        //@ ensures account_pointer(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
        //@ requires account_pointer(my_account, _);
        //@ ensures account_pointer(my_account, new_balance);
    {
        (*my_account).balance = new_balance;
    }
    unsafe fn dispose(my_account: *mut Account)
        //@ requires account_pointer(my_account, _);
        //@ ensures true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}
fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}