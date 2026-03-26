use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

impl Account {
    #[ensures(Owned::<Account>(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(Owned::<Account>(my_account))]
    #[ensures(Owned::<Account>(my_account))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        (*my_account).balance = newBalance;
    }

    #[requires(Owned::<Account>(my_account))]
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