use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

pred Account_owned(acc: *mut Account; bal: i32) =
    acc != 0 &*& (*acc).balance |-> bal;

@*/

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens result == 0 ? true : Account_owned(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ assume(my_account != 0);
        //@ close Account_owned(my_account, _);
        (*my_account).balance = 0;
        //@ open Account_owned(my_account, _);
        //@ close Account_owned(my_account, 0);
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req Account_owned(my_account, ?bal);
    //@ ens Account_owned(my_account, bal) &*& result == bal;
    {
        //@ open Account_owned(my_account, bal);
        let result = (*my_account).balance;
        //@ close Account_owned(my_account, bal);
        return result;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req Account_owned(my_account, _);
    //@ ens Account_owned(my_account, new_balance);
    {
        //@ open Account_owned(my_account, _);
        (*my_account).balance = new_balance;
        //@ close Account_owned(my_account, new_balance);
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req Account_owned(my_account, ?bal);
    //@ ens Account_owned(my_account, bal + amount);
    {
        //@ open Account_owned(my_account, bal);
        (*my_account).balance += amount;
        //@ close Account_owned(my_account, bal + amount);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_owned(my_account, _);
    //@ ens true;
    {
        //@ open Account_owned(my_account, _);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main()
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}