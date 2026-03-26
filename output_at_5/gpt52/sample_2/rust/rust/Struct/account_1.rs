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
//@ ens Account_(result, 0);
    
    
{
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    //@ close Account_(my_account, _);
    (*my_account).balance = 0;
    //@ open Account_(my_account, _);
    //@ close Account_(my_account, 0);
    my_account
}
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
//@ req Account_(my_account, _);
//@ ens Account_(my_account, new_balance);
    
    
    {
    //@ open Account_(my_account, _);
    (*my_account).balance = new_balance;
    //@ close Account_(my_account, new_balance);
    }
unsafe fn dispose(my_account: *mut Account)
//@ req Account_(my_account, _);
//@ ens true;
    
    
    {
    //@ open Account_(my_account, _);
    dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}
fn main()
    
    
{
unsafe {
    let my_account = Account::create();
    //@ assert Account_(my_account, 0);
    Account::set_balance(my_account, 5);
    //@ assert Account_(my_account, 5);
    Account::dispose(my_account);
    }
}