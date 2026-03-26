use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ requires true;
    //@ ensures result != 0 && account_pointer(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    //@ requires account_pointer(my_account, ?oldBalance);
    //@ ensures account_pointer(my_account, newBalance);
    {
        (*my_account).balance = newBalance;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ requires account_pointer(my_account, ?balance);
    //@ ensures true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

//@ predicate account_pointer(Account *p; int bal) = p |-> Account { balance: bal };

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}