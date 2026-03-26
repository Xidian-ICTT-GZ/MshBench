use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@
pred Account_balance(account: *mut Account; balance: i32) =
    (*account).balance |-> balance;

pred Account_full(account: *mut Account; balance: i32) =
    alloc_block_Account(account) &*& Account_balance(account, balance);
@*/

impl Account {
    //@ req true;
    //@ ens Account_full(result, 0);
    unsafe fn create() -> *mut Account
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close_struct(my_account);
        (*my_account).balance = 0;
        //@ close Account_balance(my_account, 0);
        //@ close Account_full(my_account, 0);
        my_account
    }

    //@ req Account_full(my_account, _);
    //@ ens Account_full(my_account, new_balance);
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    {
        //@ open Account_full(my_account, _);
        //@ open Account_balance(my_account, _);
        (*my_account).balance = new_balance;
        //@ close Account_balance(my_account, new_balance);
        //@ close Account_full(my_account, new_balance);
    }

    //@ req Account_full(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    {
        //@ open Account_full(my_account, _);
        //@ open Account_balance(my_account, _);
        //@ open_struct(my_account);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}