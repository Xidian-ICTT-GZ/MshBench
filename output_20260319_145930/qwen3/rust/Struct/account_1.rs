use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
/*@ pred Account_own(t: *mut Account) = 
    alloc_block_(t as *u8, std::mem::size_of::<Account>()) &*&
    struct_Account_padding(t) &*&
    (*t).balance |-> _;
@*/
struct Account {
    balance: i32,
}
impl Account {
//@ req true;
//@ ens Account_own(result);
unsafe fn create() -> *mut Account
    
    
{
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    //@ close Account_own(my_account);
    (*my_account).balance = 0;
    my_account
}
//@ req Account_own(my_account);
//@ ens Account_own(my_account);
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
    //@ open Account_own(my_account);
    (*my_account).balance = new_balance;
    //@ close Account_own(my_account);
    }
//@ req Account_own(my_account);
//@ ens true;
unsafe fn dispose(my_account: *mut Account)
    
    
    {
    //@ open Account_own(my_account);
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