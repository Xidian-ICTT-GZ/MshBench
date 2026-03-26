use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

/*@
predicate account_owns(ptr: *mut Account, balance: i32) =
    ptr |-> struct Account { balance: balance };
@*/

impl Account {
    #[ensures(account_owns(result, 0))]
    unsafe fn create() -> *mut Account {
        let layout = Layout::new::<Account>();
        let my_account = alloc(layout) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(layout);
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(account_owns(my_account, ?b))]
    #[ensures(account_owns(my_account, b))]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        return (*my_account).balance;
    }

    #[requires(account_owns(my_account, _))]
    #[ensures(account_owns(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(account_owns(my_account, ?b))]
    #[ensures(account_owns(my_account, b + amount))]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    #[requires(account_owns(my_account, _))]
    unsafe fn dispose(my_account: *mut Account) {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}