use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

predicate account(my_account: *mut Account) {
    my_account != 0 && struct_Account { balance: ?b }@my_account
}

impl Account {
    #[requires(Layout::new::<Account>().size() > 0)]
    #[ensures(result != 0 && account(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(account(my_account))]
    #[ensures(account(my_account))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        (*my_account).balance = newBalance;
    }

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
        Account::dispose(my_account);
    }
}