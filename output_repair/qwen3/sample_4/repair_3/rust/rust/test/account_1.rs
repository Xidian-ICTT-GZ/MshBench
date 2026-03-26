use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
struct Account {
    balance: i32,
}
predicate account_block(ptr: *mut Account; balance: i32) =
    ptr != std::ptr::null_mut() &&
    heap_block(ptr as *mut u8, Layout::new::<Account>()) &&
    (*ptr).balance |-> balance;

impl Account {
    #[ensures(account_block(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account_block(my_account, old_balance))]
    #[ensures(account_block(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account_block(my_account, _))]
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