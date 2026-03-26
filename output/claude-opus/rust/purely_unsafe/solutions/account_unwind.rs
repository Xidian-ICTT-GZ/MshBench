use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

pred Account_balance(account: *mut Account, balance: i32) =
    (*account).balance |-> balance;

pred Account(account: *mut Account, balance: i32) =
    Account_balance(account, balance);

impl Account {
    #[ensures(Account(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(Account(my_account, _))]
    #[ensures(Account(my_account, newBalance))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        (*my_account).balance = newBalance;
    }

    #[requires(Account(my_account, _))]
    unsafe fn dispose(my_account: *mut Account) {
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