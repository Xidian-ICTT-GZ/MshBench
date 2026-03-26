use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Account(account: *mut Account; balance: i32) = 
    struct_Account_balance(account, balance) &*&
    account != 0;
@*/

struct Account {
    balance: i32,
}

impl Account {
    //@ req true;
    //@ ens Account(result, 0);
    unsafe fn create() -> *mut Account
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account(my_account, _);
        (*my_account).balance = 0;
        //@ close Account(my_account, 0);
        return my_account;
    }

    //@ req Account(my_account, _);
    //@ ens Account(my_account, newBalance);
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    {
        //@ open Account(my_account, _);
        (*my_account).balance = newBalance;
        //@ close Account(my_account, newBalance);
    }

    //@ req Account(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    {
        //@ open Account(my_account, _);
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