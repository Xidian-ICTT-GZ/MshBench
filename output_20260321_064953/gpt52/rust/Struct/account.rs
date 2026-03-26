use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

pred Account_ptr(p: *mut Account; b: i32) =
    p != 0 &*& (*p).balance |-> b;

@*/

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens result == 0 ? true : Account_ptr(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ assume(my_account != 0);
        //@ close Account_ptr(my_account, _);
        (*my_account).balance = 0;
        //@ open Account_ptr(my_account, _);
        //@ close Account_ptr(my_account, 0);
        my_account
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req Account_ptr(my_account, _);
    //@ ens Account_ptr(my_account, new_balance);
    {
        //@ open Account_ptr(my_account, _);
        (*my_account).balance = new_balance;
        //@ close Account_ptr(my_account, new_balance);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_ptr(my_account, _);
    //@ ens true;
    {
        //@ open Account_ptr(my_account, _);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main()
    //@ req true;
    //@ ens true;
{
    unsafe {
        let my_account = Account::create();
        //@ assert my_account == 0 ? true : Account_ptr(my_account, 0);
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}