use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
/*@

pred account(p: *mut Account; b: i32) =
    malloc_block_Account(p) &*& struct_Account_balance(p, b);

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
    //@ close_struct(my_account);
    (*my_account).balance = 0;
    //@ close account(my_account, 0);
    my_account
}
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
//@ req account(my_account, _);
//@ ens account(my_account, new_balance);
    
    
    {
    //@ open account(my_account, _);
    //@ open_struct(my_account);
    (*my_account).balance = new_balance;
    //@ close_struct(my_account);
    //@ close account(my_account, new_balance);
    }
unsafe fn dispose(my_account: *mut Account)
//@ req account(my_account, _);
//@ ens true;
    
    
    {
    //@ open account(my_account, _);
    //@ open_struct(my_account);
    //@ open malloc_block_Account(my_account);
    dealloc(my_account as *mut u8, Layout::new::<Account>());
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