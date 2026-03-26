use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    /*@
    pred account_pred(account_ptr: *mut Account) = malloc_block<Account>(account_ptr, 1);
    @*/

    unsafe fn create() -> *mut Account
    
    //@ req true;
    //@ ens account_pred(result);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    
    //@ req account_pred(my_account);
    //@ ens account_pred(my_account);
    {
        (*my_account).balance = newBalance;
    }

    unsafe fn dispose(my_account: *mut Account)
    
    //@ req account_pred(my_account);
    //@ ens true;
    {
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