use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

/*@
pred Account_balance(my_account: *mut Account; balance: i32) =
    my_account != null &*& my_account->balance |-> balance;
@*/

impl Account {
    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens Account_balance(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        //@ close Account_balance(my_account, 0);
        my_account
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req Account_balance(my_account, _);
    //@ ens Account_balance(my_account, new_balance);
    {
        //@ open Account_balance(my_account, _);
        (*my_account).balance = new_balance;
        //@ close Account_balance(my_account, new_balance);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_balance(my_account, _);
    //@ ens true;
    {
        //@ open Account_balance(my_account, _);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}