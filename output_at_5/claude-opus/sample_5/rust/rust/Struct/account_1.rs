use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
impl Account {
    /*
    //@ pred account(account_ptr: *mut Account, bal: i32) =
    //@     acc(account_ptr as usize, sizeof::<Account>()) &*&
    //@     account_ptr->balance |-> bal;
    */
    unsafe fn create() -> *mut Account
    //@ requires true;
    //@ ensures account(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ requires account(my_account, _);
    //@ ensures account(my_account, new_balance);
    {
        (*my_account).balance = new_balance;
    }
    unsafe fn dispose(my_account: *mut Account)
    //@ requires account(my_account, _);
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