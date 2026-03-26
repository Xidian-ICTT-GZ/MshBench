use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr;

struct Account {
    balance: i32,
}

predicate account_owned(ptr: *mut Account) =
    ptr != ptr::null_mut() &*&
    heap_block(ptr as *mut u8, std::mem::size_of::<Account>());

impl Account {
    #[ensures(account_owned(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account_owned(my_account))]
    #[ensures(account_owned(my_account))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account_owned(my_account))]
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