use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

pred account(p: *mut Account; bal: i32) =
    std::alloc::alloc_block(p as *mut u8, Layout::new::<Account>()) &*&
    (*p).balance |-> bal;

@*/

impl Account {
//@ req true;
//@ ens result == std::ptr::null_mut::<Account>() ? true : account(result, 0);
unsafe fn create() -> *mut Account
    
    
{
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    //@ close account(my_account, _);
    //@ open account(my_account, _);
    (*my_account).balance = 0;
    //@ close account(my_account, 0);
    my_account
}
//@ req account(my_account, _);
//@ ens account(my_account, new_balance);
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
    //@ open account(my_account, _);
    (*my_account).balance = new_balance;
    //@ close account(my_account, new_balance);
    }
//@ req account(my_account, _);
//@ ens true;
unsafe fn dispose(my_account: *mut Account)
    
    
    {
    //@ open account(my_account, _);
    dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main()
    
    
{
unsafe {
    let my_account = Account::create();
    //@ open account(my_account, 0);
    //@ close account(my_account, 0);
    Account::set_balance(my_account, 5);
    Account::dispose(my_account);
    }
}