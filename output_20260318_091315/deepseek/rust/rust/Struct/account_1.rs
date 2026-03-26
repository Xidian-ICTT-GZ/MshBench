use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

#[predicate]
fn account_points_to(ptr: *mut Account, balance: i32) -> bool {
    unsafe {
        ptr != std::ptr::null_mut() &&
        (*ptr).balance == balance &&
        full_perm(ptr)
    }
}

#[predicate]
fn layout_account() -> bool {
    Layout::new::<Account>().size() == std::mem::size_of::<Account>() &&
    Layout::new::<Account>().align() == std::mem::align_of::<Account>()
}

impl Account {
    #[requires(layout_account())]
    #[ensures(|result| account_points_to(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account_points_to(my_account, _old_balance))]
    #[ensures(account_points_to(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account_points_to(my_account, _balance))]
    #[ensures(layout_account())]
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