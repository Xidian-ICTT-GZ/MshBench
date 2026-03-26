use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

pred account(p: *mut Account; bal: i32) =
    malloc_block_Account(p) &*&
    (*p).balance |-> bal;

@*/

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens account(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close account(my_account, _);
        (*my_account).balance = 0;
        //@ open account(my_account, _);
        //@ close account(my_account, 0);
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req account(my_account, ?bal);
    //@ ens account(my_account, bal) &*& result == bal;
    {
        //@ open account(my_account, bal);
        let res = (*my_account).balance;
        //@ close account(my_account, bal);
        return res;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req account(my_account, _);
    //@ ens account(my_account, new_balance);
    {
        //@ open account(my_account, _);
        (*my_account).balance = new_balance;
        //@ close account(my_account, new_balance);
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req account(my_account, ?bal);
    //@ ens account(my_account, bal + amount);
    {
        //@ open account(my_account, bal);
        (*my_account).balance += amount;
        //@ close account(my_account, bal + amount);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req account(my_account, _);
    //@ ens true;
    {
        //@ open account(my_account, _);
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
        //@ assert b == 15;
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}