use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred account(t: *mut Account, balance: i32) = 
    alloc_block(t, std::mem::size_of::<Account>()) &*& 
    struct_Account_padding(t) &*& 
    (*t).balance |-> balance;
@*/

/*@ pred struct_Account_padding(t: *mut Account) = true; @*/

struct Account {
    balance: i32,
}

impl Account {

    //@ req true;
    //@ ens account(result, 0);
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        //@ close account(my_account, 0);
        return my_account;
    }

    //@ req account(my_account, _);
    //@ ens account(my_account, newBalance);
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    
    
    
    {
        //@ open account(my_account, _);
        (*my_account).balance = newBalance;
        //@ close account(my_account, newBalance);
    }

    //@ req account(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open account(my_account, _);
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