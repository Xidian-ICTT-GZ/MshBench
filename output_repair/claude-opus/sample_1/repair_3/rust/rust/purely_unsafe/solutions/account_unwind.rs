use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate account_owned(p: *mut Account) = true;

struct Account {
    balance: i32,
}

impl Account {
    unsafe fn create() -> *mut Account
        ensures account_owned(result)
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
        requires account_owned(my_account)
        ensures account_owned(my_account)
    {
        (*my_account).balance = newBalance;
    }

    unsafe fn dispose(my_account: *mut Account)
        requires account_owned(my_account)
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