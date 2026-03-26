use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

/*@

predicate Account_(ptr: *mut Account, bal: i32) =
    ptr as *mut i32 |-> bal;

@*/

impl Account {
    #[requires(true)]
    #[ensures(result as *mut i32 |-> 0)]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(my_account as *mut i32 |-> ?bal)]
    #[ensures(my_account as *mut i32 |-> bal &*& result == bal)]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        return (*my_account).balance;
    }

    #[requires(my_account as *mut i32 |-> _)]
    #[ensures(my_account as *mut i32 |-> new_balance)]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        (*my_account).balance = new_balance;
    }

    #[requires(my_account as *mut i32 |-> ?bal)]
    #[ensures(my_account as *mut i32 |-> (bal + amount))]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    #[requires(my_account as *mut i32 |-> _)]
    #[ensures(true)]
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