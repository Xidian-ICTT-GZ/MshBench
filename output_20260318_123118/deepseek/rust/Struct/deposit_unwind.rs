use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

predicate account(my_account: *mut Account) {
    |-> my_account.balance: i32
}

impl Account {
    #[requires(Layout::new::<Account>().size() > 0)]
    #[ensures(result != std::ptr::null_mut())]
    #[ensures(account(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(my_account != std::ptr::null_mut())]
    #[requires(account(my_account))]
    #[ensures(account(my_account))]
    #[ensures(result == old((*my_account).balance))]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        return (*my_account).balance;
    }

    #[requires(my_account != std::ptr::null_mut())]
    #[requires(account(my_account))]
    #[ensures(|-> my_account.balance: new_balance)]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(my_account != std::ptr::null_mut())]
    #[requires(account(my_account))]
    #[ensures(|-> my_account.balance: old((*my_account).balance) + amount)]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    #[requires(my_account != std::ptr::null_mut())]
    #[requires(account(my_account))]
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