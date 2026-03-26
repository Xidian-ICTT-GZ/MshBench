use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

pred account(my_account: *mut Account; balance: i32) =
    std::alloc::alloc_block(my_account as *mut u8, Layout::new_::<Account>()) &*&
    (*my_account).balance |-> balance;

@*/

impl Account {

    //@ req true;
    //@ ens result == 0 ? true : account(result, 0);
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close account(my_account, 0);
        (*my_account).balance = 0;
        return my_account;
    }

    //@ req account(my_account, ?b);
    //@ ens account(my_account, b) &*& result == b;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    
    
    
    {
        //@ open account(my_account, b);
        let r = (*my_account).balance;
        //@ close account(my_account, b);
        return r;
    }

    //@ req account(my_account, _);
    //@ ens account(my_account, new_balance);
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    
    {
        //@ open account(my_account, _);
        (*my_account).balance = new_balance;
        //@ close account(my_account, new_balance);
    }

    //@ req account(my_account, ?b);
    //@ ens account(my_account, b + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    
    
    
    {
        //@ open account(my_account, b);
        (*my_account).balance += amount;
        //@ close account(my_account, b + amount);
    }

    //@ req account(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open account(my_account, _);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
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