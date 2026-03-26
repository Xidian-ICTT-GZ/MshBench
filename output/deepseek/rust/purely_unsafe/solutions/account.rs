use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

// Predicate for ownership of a single Account on the heap
predicate account(my_account: *mut Account; balance: i32) {
    my_account != 0 && struct_Account_balance(my_account, balance)
}

// Predicate for the balance field of Account
predicate struct_Account_balance(my_account: *mut Account, balance: i32) {
    my_account != 0 && points_to(my_account.balance, balance)
}

impl Account {
    #[requires(layout.size() == std::mem::size_of::<Account>())]
    #[requires(layout.align() == std::mem::align_of::<Account>())]
    #[ensures(result != 0)]
    #[ensures(account(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account(my_account, _))]
    #[ensures(account(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account(my_account, _))]
    #[ensures(true)]
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