use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
//@ pred account(account: *mut Account, balance: i32) = account as *mut u8 |->? _ &*& struct_Account_padding(account);
impl Account {
unsafe fn create() -> *mut Account
    
    
{
    //@ req true;
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    (*my_account).balance = 0;
    //@ close account(my_account, 0);
    //@ ens account(result, 0);
    my_account
}
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
    //@ req account(my_account, _);
    //@ open account(my_account, _);
    (*my_account).balance = new_balance;
    //@ close account(my_account, new_balance);
    //@ ens account(my_account, new_balance);
    }
unsafe fn dispose(my_account: *mut Account)
    
    
    {
    //@ req account(my_account, _);
    //@ open account(my_account, _);
    dealloc(my_account as *mut u8, Layout::new::<Account>());
    //@ ens true;
    }
}
fn main()
    
    
{
unsafe {
    let my_account = Account::create();
    Account::set_balance(my_account, 5);
    Account::dispose(my_account);
    }
}