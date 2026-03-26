use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
impl Account {
unsafe fn create() -> *mut Account
    
    
{
    //@ req true;
    //@ ens ptr::<Account>(result, _);
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    //@ open ptr::<Account>(my_account, _);
    (*my_account).balance = 0;
    //@ close ptr::<Account>(my_account, Account { balance: 0 });
    my_account
}
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
    //@ req ptr::<Account>(my_account, _);
    //@ ens ptr::<Account>(my_account, Account { balance: new_balance });
    //@ open ptr::<Account>(my_account, _);
    (*my_account).balance = new_balance;
    //@ close ptr::<Account>(my_account, Account { balance: new_balance });
    }
unsafe fn dispose(my_account: *mut Account)
    
    
    {
    //@ req ptr::<Account>(my_account, _);
    //@ ens true;
    //@ open ptr::<Account>(my_account, _);
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