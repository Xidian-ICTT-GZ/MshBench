use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

predicate Account_owning(ptr: *mut Account) = 
    ptr as usize != 0 &*& 
    std::alloc::alloc_block(ptr as *u8, std::alloc::Layout::new::<Account>());

impl Account {
    #[requires(true)]
    #[ensures(Account_owning(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(Account_owning(my_account))]
    #[ensures(Account_owning(my_account))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        (*my_account).balance = newBalance;
    }

    #[requires(Account_owning(my_account))]
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