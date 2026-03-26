use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens result != std::ptr::null_mut::<Account>() ? *result |-> Account{balance: 0} : true;
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ assert my_account != std::ptr::null_mut::<Account>();
        //@ close_struct(my_account);
        (*my_account).balance = 0;
        //@ open_struct(my_account);
        //@ close_struct(my_account);
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    //@ req my_account != std::ptr::null_mut::<Account>() &*& *my_account |-> Account{balance: _};
    //@ ens *my_account |-> Account{balance: newBalance};
    {
        //@ open_struct(my_account);
        (*my_account).balance = newBalance;
        //@ close_struct(my_account);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req my_account != std::ptr::null_mut::<Account>() &*& *my_account |-> Account{balance: _};
    //@ ens true;
    {
        //@ open_struct(my_account);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let my_account = Account::create();
        //@ assert my_account != std::ptr::null_mut::<Account>();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}