use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@
predicate account_own(account: *mut Account; balance: i32) =
    struct_Account_padding(account) &*&
    (*account).balance |-> balance;
@*/

impl Account {
    #[requires(Layout::new::<Account>().size() > 0)]
    #[ensures(result != 0 as *mut Account)]
    #[ensures(account_own(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account_own(my_account, _))]
    #[ensures(account_own(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account_own(my_account, _))]
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