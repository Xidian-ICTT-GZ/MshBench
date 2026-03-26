use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

pred Account_(p: *mut Account; b: i32) =
    alloc_block(p as *u8, Layout::new_::<Account>()) &*&
    struct Account { balance: b }(p);

@*/

impl Account {
//@ req true;
//@ ens result == 0 ? true : Account_(result, 0);
unsafe fn create() -> *mut Account
    
    
{
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    //@ assume(!my_account.is_null());
    //@ close_struct(my_account);
    (*my_account).balance = 0;
    //@ close Account_(my_account, 0);
    my_account
}

//@ req Account_(my_account, _);
//@ ens Account_(my_account, new_balance);
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
    //@ open Account_(my_account, _);
    //@ open_struct(my_account);
    (*my_account).balance = new_balance;
    //@ close_struct(my_account);
    //@ close Account_(my_account, new_balance);
    }

//@ req Account_(my_account, _);
//@ ens true;
unsafe fn dispose(my_account: *mut Account)
    
    
    {
    //@ open Account_(my_account, _);
    //@ open_struct(my_account);
    dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main()
    
    
{
unsafe {
    let my_account = Account::create();
    //@ assume(my_account != 0);
    //@ open Account_(my_account, 0);
    //@ close Account_(my_account, 0);
    Account::set_balance(my_account, 5);
    Account::dispose(my_account);
    }
}