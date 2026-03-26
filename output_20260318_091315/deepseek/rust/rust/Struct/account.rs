use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

predicate account_own(ptr: *mut Account, balance: i32) {
    ptr != 0 && struct_account_ptr_balance(ptr, balance)
}

predicate struct_account_ptr_balance(ptr: *mut Account, balance: i32) {
    let ptr_balance = &(*ptr).balance;
    ptr_balance.is_slice() && ptr_balance.len() == 1 && ptr_balance[0] == balance
}

impl Account {
    #[requires(Layout::new::<Account>().size() > 0)]
    #[ensures(result != 0)]
    #[ensures(account_own(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account_own(my_account, _old_balance))]
    #[ensures(account_own(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account_own(my_account, _balance))]
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