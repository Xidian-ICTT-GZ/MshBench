use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
//@ predicate_ctor Account_own(account: *mut Account, balance: i32)() = (*account).balance |-> balance;

impl Account {
unsafe fn create() -> *mut Account
    
    
{
    //@ req true;
    //@ ens result != 0 as *mut Account &*& Account_own(result, 0)();
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    (*my_account).balance = 0;
    //@ close Account_own(my_account, 0)();
    my_account
}
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
    //@ req Account_own(my_account, _)();
    //@ ens Account_own(my_account, new_balance)();
    //@ open Account_own(my_account, _)();
    (*my_account).balance = new_balance;
    //@ close Account_own(my_account, new_balance)();
    }
unsafe fn dispose(my_account: *mut Account)
    
    
    {
    //@ req Account_own(my_account, _)();
    //@ ens true;
    //@ open Account_own(my_account, _)();
    dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}
fn main()
    
    
{
unsafe {
    //@ req true;
    //@ ens true;
    let my_account = Account::create();
    Account::set_balance(my_account, 5);
    Account::dispose(my_account);
    }
}