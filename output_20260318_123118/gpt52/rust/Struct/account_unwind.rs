use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@

predicate account(p: *mut Account; bal: i32) =
    (*p).balance |-> bal;

@*/

impl Account {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() &*& account(result, 0))]
    unsafe fn create() -> *mut Account
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(account(my_account, _))]
    #[ensures(account(my_account, newBalance))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    {
        (*my_account).balance = newBalance;
    }

    #[requires(account(my_account, _))]
    #[ensures(true)]
    unsafe fn dispose(my_account: *mut Account)
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}