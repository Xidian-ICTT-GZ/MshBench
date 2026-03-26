use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

predicate AccountPtr(ptr: *mut Account; bal: i32) =
    ptr->balance |-> bal;

@*/

impl Account {
    unsafe fn create() -> *mut Account
    //@ requires true;
    //@ ensures AccountPtr(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ requires AccountPtr(my_account, ?bal);
    //@ ensures AccountPtr(my_account, bal) &*& result == bal;
    {
        return (*my_account).balance;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ requires AccountPtr(my_account, _);
    //@ ensures AccountPtr(my_account, new_balance);
    {
        (*my_account).balance = new_balance;
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ requires AccountPtr(my_account, ?bal);
    //@ ensures AccountPtr(my_account, bal + amount);
    {
        (*my_account).balance += amount;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ requires AccountPtr(my_account, _);
    //@ ensures true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}