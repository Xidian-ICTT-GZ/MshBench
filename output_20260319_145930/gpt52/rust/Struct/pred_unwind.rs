use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

/*@

pred Account_ptr(p: *mut Account; limit: i32, balance: i32) =
    alloc_block(p as *u8, Layout::new::<Account>()) &*&
    (*p).limit |-> limit &*&
    (*p).balance |-> balance;

@*/

impl Account {

    //@ req true;
    //@ ens result == 0 ? true : Account_ptr(result, limit, 0);
    unsafe fn create(limit: i32) -> *mut Account
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        //@ close Account_ptr(my_account, limit, 0);
        my_account
    }

    //@ req Account_ptr(my_account, ?limit, ?balance);
    //@ ens Account_ptr(my_account, limit, balance) &*& result == balance;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    {
        //@ open Account_ptr(my_account, ?limit, ?balance);
        let result = (*my_account).balance;
        //@ close Account_ptr(my_account, limit, balance);
        result
    }

    //@ req Account_ptr(my_account, ?limit, ?balance);
    //@ ens Account_ptr(my_account, limit, balance + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    {
        //@ open Account_ptr(my_account, ?limit, ?balance);
        (*my_account).balance += amount;
        //@ close Account_ptr(my_account, limit, balance + amount);
    }

    //@ req Account_ptr(my_account, ?limit, ?balance);
    //@ ens Account_ptr(my_account, limit, balance - result) &*& (balance - amount < limit ? result == balance - limit : result == amount);
    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32
    {
        //@ open Account_ptr(my_account, ?limit, ?balance);
        let result =
            if (*my_account).balance - amount < (*my_account).limit {
                (*my_account).balance - (*my_account).limit
            } else {
                amount
            };
        (*my_account).balance -= result;
        //@ close Account_ptr(my_account, limit, balance - result);
        result
    }

    //@ req Account_ptr(my_account, ?limit, ?balance);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    {
        //@ open Account_ptr(my_account, limit, balance);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main()
{
    unsafe {
        let my_account = Account::create(-100);
        //@ assume(my_account != 0);
        Account::deposit(my_account, 200);
        let w1 = Account::withdraw(my_account, 50);
        std::hint::assert_unchecked(w1 == 50);
        let b1 = Account::get_balance(my_account);
        std::hint::assert_unchecked(b1 == 150);
        let w2 = Account::withdraw(my_account, 300);
        std::hint::assert_unchecked(w2 == 250);
        let b2 = Account::get_balance(my_account);
        std::hint::assert_unchecked(b2 == -100);
        Account::dispose(my_account);
    }
}