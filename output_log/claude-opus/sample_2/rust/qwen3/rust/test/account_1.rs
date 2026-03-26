use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred account_pred(p: *mut Account) =
    p != 0 &*&
    malloc_block_Account(p, 1) &*&
    (*p).balance |-> ?b
]

struct Account {
    balance: i32,
}

impl Account {
    #[requires(Layout::new::<Account>().size() > 0)]
    #[ensures(account_pred(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account_pred(my_account))]
    #[ensures(account_pred(my_account))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account_pred(my_account))]
    #[ensures(true)] // deallocation frees the block, no leftover ownership
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