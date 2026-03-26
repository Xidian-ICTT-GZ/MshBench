use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

#[predicate]
fn account_own(ptr: *mut Account, balance: i32) -> bool {
    unsafe {
        (*ptr).balance == balance
    }
}

#[predicate]
fn account_full(ptr: *mut Account) -> bool {
    exists(|balance: i32| account_own(ptr, balance))
}

impl Account {
    #[requires(Layout::new::<Account>().size() > 0)]
    #[ensures(result != std::ptr::null_mut())]
    #[ensures(account_full(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        proof_lemma!{ my_account };
        return my_account;
    }

    #[requires(account_full(my_account))]
    #[ensures(account_full(my_account))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        (*my_account).balance = newBalance;
        proof_lemma!{ my_account };
    }

    #[requires(account_full(my_account))]
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