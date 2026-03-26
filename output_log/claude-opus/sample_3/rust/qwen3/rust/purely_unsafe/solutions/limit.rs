use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred account_pred(p: *mut Account, limit: i32, balance: i32) = 
    p != 0 &*& 
    *p |-> Account { limit: limit, balance: balance } &*&
    malloc_block_Account(p)
]

#[lemma]
fn account_pred_unique(p: *mut Account, limit1: i32, balance1: i32, limit2: i32, balance2: i32)
    requires account_pred(p, limit1, balance1), account_pred(p, limit2, balance2)
    ensures limit1 == limit2 && balance1 == balance2
{
    // VeriFast can infer this via structural equality of the predicate
}

struct Account {
    limit: i32,
    balance: i32,
}

impl Account {
    #[requires(Layout::new::<Account>().size() > 0)]
    #[ensures(account_pred(result, limit, 0))]
    unsafe fn create(limit: i32) -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        my_account
    }

    #[requires(account_pred(my_account, limit, balance))]
    #[ensures(account_pred(my_account, limit, balance) &*& result == balance)]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        (*my_account).balance
    }

    #[requires(account_pred(my_account, limit, balance))]
    #[ensures(account_pred(my_account, limit, balance + amount))]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    #[requires(account_pred(my_account, limit, balance))]
    #[ensures(account_pred(my_account, limit, balance - result) &*&
              ((result == amount && balance - amount >= limit) ||
               (result == balance - limit && balance - amount < limit)))]
    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32 {
        let result = if (*my_account).balance - amount < (*my_account).limit {
            (*my_account).balance - (*my_account).limit
        } else {
            amount
        };
        (*my_account).balance -= result;
        result
    }

    #[requires(account_pred(my_account, limit, balance))]
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