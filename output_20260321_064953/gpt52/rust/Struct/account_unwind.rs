use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens result != std::ptr::null_mut::<Account>() &*& (*result).balance |-> 0;
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    //@ req my_account != std::ptr::null_mut::<Account>() &*& (*my_account).balance |-> _;
    //@ ens (*my_account).balance |-> newBalance;
    {
        (*my_account).balance = newBalance;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req my_account != std::ptr::null_mut::<Account>() &*& (*my_account).balance |-> _;
    //@ ens true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}