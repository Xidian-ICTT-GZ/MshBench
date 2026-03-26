use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

predicate account(my_account: *mut Account; limit: i32, balance: i32) {
    my_account != 0 && struct_account(my_account) && 
    (*my_account).limit |-> limit && (*my_account).balance |-> balance
}

impl Account {
    #[requires(limit <= 0)]
    #[ensures(result != 0)]
    #[ensures(account(result, limit, 0))]
    unsafe fn create(limit: i32) -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        
        my_account
    }

    #[requires(account(my_account, limit, balance))]
    #[ensures(account(my_account, limit, balance))]
    #[ensures(result == balance)]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        let result = (*my_account).balance;
        
        result
    }

    #[requires(account(my_account, limit, balance))]
    #[requires(balance + amount >= limit)]
    #[ensures(account(my_account, limit, balance + amount))]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    #[requires(account(my_account, limit, balance))]
    #[requires(amount >= 0)]
    #[ensures(account(my_account, limit, balance - result))]
    #[ensures(result >= 0)]
    #[ensures(result <= amount)]
    #[ensures(balance - result >= limit)]
    #[ensures(result == amount || result == balance - limit)]
    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32 {
        let result =
            if (*my_account).balance - amount < (*my_account).limit {
                (*my_account).balance - (*my_account).limit
            } else {
                amount
            };
        (*my_account).balance -= result;
        
        result
    }

    #[requires(account(my_account, _, _))]
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