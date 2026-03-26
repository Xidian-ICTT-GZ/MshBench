use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred account(p: *mut Account, balance: i32) = 
    alloc_block_(p as *mut u8, std::mem::size_of::<Account>()) &*&
    struct_Account_padding(p) &*&
    (*p).balance |-> balance;
@*/

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
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}