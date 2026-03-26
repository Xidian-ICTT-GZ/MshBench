use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

//@ predicate_unsafe Account_own(account: *mut Account; balance: i32) = (*account).balance |-> balance;

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens Account_own(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account_own(my_account, _);
        (*my_account).balance = 0;
        //@ close Account_own(my_account, 0);
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    //@ req Account_own(my_account, _);
    //@ ens Account_own(my_account, newBalance);
    {
        //@ open Account_own(my_account, _);
        (*my_account).balance = newBalance;
        //@ close Account_own(my_account, newBalance);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_own(my_account, _);
    //@ ens true;
    {
        //@ open Account_own(my_account, _);
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