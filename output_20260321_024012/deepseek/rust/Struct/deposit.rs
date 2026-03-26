use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

//@ predicate_unsafe Account_own(account: *mut Account, balance: i32) = (*account).balance |-> balance;

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

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req Account_own(my_account, ?balance);
    //@ ens Account_own(my_account, balance) &*& result == balance;
    {
        //@ open Account_own(my_account, _);
        return (*my_account).balance;
        //@ close Account_own(my_account, _);
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req Account_own(my_account, _);
    //@ ens Account_own(my_account, new_balance);
    {
        //@ open Account_own(my_account, _);
        (*my_account).balance = new_balance;
        //@ close Account_own(my_account, new_balance);
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req Account_own(my_account, ?balance);
    //@ ens Account_own(my_account, balance + amount);
    {
        //@ open Account_own(my_account, ?old_balance);
        (*my_account).balance += amount;
        //@ close Account_own(my_account, old_balance + amount);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_own(my_account, _);
    //@ ens true;
    {
        //@ open Account_own(my_account, _);
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
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}