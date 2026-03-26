use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

// VeriFast predicates
#[predicate]
fn account_own(account: *mut Account, balance: i32) -> bool {
    unsafe {
        (*account).balance == balance
    }
}

#[predicate]
fn account_full(account: *mut Account, balance: i32) -> bool {
    account_own(account, balance) && 
    malloc_block_account(account)
}

#[predicate]
fn malloc_block_account(account: *mut Account) -> bool {
    true // VeriFast built-in for allocation block
}

impl Account {
    #[requires(true)]
    #[ensures(result != 0 as *mut Account)]
    #[ensures(account_full(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(account_full(my_account, old_balance))]
    #[ensures(account_full(my_account, newBalance))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        (*my_account).balance = newBalance;
    }

    #[requires(account_full(my_account, _balance))]
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