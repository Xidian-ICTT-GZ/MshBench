use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@
pred Account_balance(p: *mut Account; v: i32) =
    (*p).balance |-> v;

pred Account_full(p: *mut Account; v: i32) =
    alloc_block_Account(p) &*& Account_balance(p, v);
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
        //@ close Account_balance(my_account, _);
        (*my_account).balance = 0;
        //@ close Account_full(my_account, 0);
        return my_account;
    }

    //@ req Account_full(my_account, ?v);
    //@ ens Account_full(my_account, v) &*& result == v;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    {
        //@ open Account_full(my_account, v);
        //@ open Account_balance(my_account, v);
        let result = (*my_account).balance;
        //@ close Account_balance(my_account, v);
        //@ close Account_full(my_account, v);
        return result;
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

    //@ req Account_full(my_account, ?v);
    //@ ens Account_full(my_account, v + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    {
        //@ open Account_full(my_account, v);
        //@ open Account_balance(my_account, v);
        (*my_account).balance += amount;
        //@ close Account_balance(my_account, v + amount);
        //@ close Account_full(my_account, v + amount);
    }

    //@ req Account_full(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    {
        //@ open Account_full(my_account, _);
        //@ open Account_balance(my_account, _);
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