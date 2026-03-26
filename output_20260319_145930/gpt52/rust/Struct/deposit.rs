use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred Account_(p: *mut Account; bal: i32) =
    alloc_block(p, Layout::new::<Account>()) &*&
    (*p).balance |-> bal;

@*/

struct Account {
    balance: i32,
}

impl Account {

    //@ req true;
    //@ ens result != 0 &*& Account_(result, 0);
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account_(my_account, _);
        (*my_account).balance = 0;
        //@ open Account_(my_account, _);
        //@ close Account_(my_account, 0);
        return my_account;
    }

    //@ req Account_(my_account, ?bal);
    //@ ens Account_(my_account, bal) &*& result == bal;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    
    
    {
        //@ open Account_(my_account, bal);
        let r = (*my_account).balance;
        //@ close Account_(my_account, bal);
        return r;
    }

    //@ req Account_(my_account, _);
    //@ ens Account_(my_account, new_balance);
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
        //@ open Account_(my_account, _);
        (*my_account).balance = new_balance;
        //@ close Account_(my_account, new_balance);
    }

    //@ req Account_(my_account, ?bal);
    //@ ens Account_(my_account, bal + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    
    
    {
        //@ open Account_(my_account, bal);
        (*my_account).balance += amount;
        //@ close Account_(my_account, bal + amount);
    }

    //@ req Account_(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open Account_(my_account, _);
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
        //@ assert b == 15;
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}