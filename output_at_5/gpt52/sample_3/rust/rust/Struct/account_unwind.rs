use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

pred Account_(p: *mut Account; b: i32) =
    (*p).balance |-> b;

@*/

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens result == 0 || Account_(result, 0);
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        //@ close Account_(my_account, 0);
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    //@ req Account_(my_account, ?b);
    //@ ens Account_(my_account, newBalance);
    
    
    
    {
        //@ open Account_(my_account, b);
        (*my_account).balance = newBalance;
        //@ close Account_(my_account, newBalance);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_(my_account, ?b);
    //@ ens true;
    
    
    {
        //@ open Account_(my_account, b);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}