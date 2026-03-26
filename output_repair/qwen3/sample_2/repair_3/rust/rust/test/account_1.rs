use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[verifast::predicate]
pub fn account_owns(ptr: *mut Account) {
    std::ptr::addr_of!((*ptr).balance) |-> _ &&
    heap_block(ptr as *mut u8, Layout::new::<Account>())
}

struct Account {
    balance: i32,
}

impl Account {
    #[verifast::ensures(account_owns(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[verifast::requires(account_owns(my_account))]
    #[verifast::ensures(account_owns(my_account))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[verifast::requires(account_owns(my_account))]
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