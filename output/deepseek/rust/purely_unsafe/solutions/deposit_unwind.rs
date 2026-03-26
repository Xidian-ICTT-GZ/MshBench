use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

predicate account(my_account: *mut Account, balance: i32) {
    my_account != std::ptr::null_mut() &&
    struct_Account_balance(my_account, balance)
}

predicate struct_Account_balance(my_account: *mut Account, balance: i32) {
    my_account != std::ptr::null_mut() &&
    &raw (*my_account).balance |-> balance
}

impl Account {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && account(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(account(my_account, balance))]
    #[ensures(account(my_account, balance) && result == balance)]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        return (*my_account).balance;
    }

    #[requires(account(my_account, _old_balance))]
    #[ensures(account(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account(my_account, old_balance))]
    #[ensures(account(my_account, old_balance + amount))]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    #[requires(account(my_account, _balance))]
    #[ensures(true)]
    unsafe fn dispose(my_account: *mut Account) {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}