use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate Account_pred(*mut Account account; i32 limit, i32 balance) =
    alloc_block(account as *u8, std::mem::size_of::<Account>()) &*&
    struct_Account_padding(account) &*&
    (*account).limit |-> limit &*&
    (*account).balance |-> balance;

struct Account {
    limit: i32,
    balance: i32,
}

impl Account {
    #[requires(true)]
    #[ensures(Account_pred(result, limit, 0))]
    unsafe fn create(limit: i32) -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        my_account
    }

    #[requires(Account_pred(my_account, ?limit, ?balance))]
    #[ensures(Account_pred(my_account, limit, balance) &*& result == balance)]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        (*my_account).balance
    }

    #[requires(Account_pred(my_account, ?limit, ?balance))]
    #[ensures(Account_pred(my_account, limit, balance + amount))]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    #[requires(Account_pred(my_account, ?limit, ?balance))]
    #[ensures(match balance - amount < limit {
        true => Account_pred(my_account, limit, limit) &*& result == balance - limit,
        false => Account_pred(my_account, limit, balance - amount) &*& result == amount
    })]
    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32 {
        let result = if (*my_account).balance - amount < (*my_account).limit {
            (*my_account).balance - (*my_account).limit
        } else {
            amount
        };
        (*my_account).balance -= result;
        result
    }

    #[requires(Account_pred(my_account, ?limit, ?balance))]
    #[ensures(true)]
    unsafe fn dispose(my_account: *mut Account) {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    unsafe {
        let my_account = Account::create(-100);
        Account::deposit(my_account, 200);
        let w1 = Account::withdraw(my_account, 50);
        std::hint::assert_unchecked(w1 == 50);
        let b1 = Account::get_balance(my_account);
        std::hint::assert_unchecked(b1 == 150);
        let w2 = Account::withdraw(my_account, 300);
        std::hint::assert_unchecked(w2 == 250);
        let b2 = Account::get_balance(my_account);
        std::hint::assert_unchecked(b2 == -100);
        Account::dispose(my_account);
    }
}