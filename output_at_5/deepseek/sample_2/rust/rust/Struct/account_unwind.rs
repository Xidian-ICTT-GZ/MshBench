use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

//@ predicate Account_own(Account *a) = a.balance |-> _;

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens Account_own(result);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account_own(my_account);
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    //@ req Account_own(my_account);
    //@ ens Account_own(my_account);
    {
        //@ open Account_own(my_account);
        (*my_account).balance = newBalance;
        //@ close Account_own(my_account);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_own(my_account);
    //@ ens true;
    {
        //@ open Account_own(my_account);
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