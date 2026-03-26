use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ requires true;
    //@ ensures result != std::ptr::null_mut::<Account>() && pointer(result, _) &*& account(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ requires pointer(my_account, _) &*& account(my_account, _);
    //@ ensures pointer(my_account, _) &*& account(my_account, new_balance);
    {
        (*my_account).balance = new_balance;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ requires pointer(my_account, _) &*& account(my_account, _);
    //@ ensures true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

//@ predicate pointer(Account* p, void* v) = true; // placeholder predicate for raw pointer validity

//@ predicate account(Account* acc, int bal) = acc->balance |-> bal;

fn main()
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}