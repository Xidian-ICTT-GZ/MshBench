use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred Account_own(p: *mut Account; bal: i32) =
    alloc_block(p as *mut u8, Layout::new::<Account>()) &*&
    (*p).balance |-> bal;

@*/

struct Account {
    balance: i32,
}

impl Account {

    //@ req true;
    //@ ens result == std::ptr::null_mut() ? true : Account_own(result, 0);
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account_own(my_account, _);
        //@ open Account_own(my_account, _);
        (*my_account).balance = 0;
        //@ close Account_own(my_account, 0);
        return my_account;
    }

    //@ req Account_own(my_account, _);
    //@ ens Account_own(my_account, newBalance);
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    
    
    
    {
        //@ open Account_own(my_account, _);
        (*my_account).balance = newBalance;
        //@ close Account_own(my_account, newBalance);
    }

    //@ req Account_own(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open Account_own(my_account, _);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let my_account = Account::create();
        //@ assert my_account == std::ptr::null_mut() ? true : Account_own(my_account, 0);
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}