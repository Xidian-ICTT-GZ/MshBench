use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

//@ pred account(p: *mut Account) = (*p).balance |-> ?b &*& b >= 0;

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens account(result);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        //@ close account(my_account);
        my_account
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req account(my_account);
    //@ ens account(my_account);
    {
        //@ open account(my_account);
        (*my_account).balance = new_balance;
        //@ close account(my_account);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req account(my_account);
    //@ ens true;
    {
        //@ open account(my_account);
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