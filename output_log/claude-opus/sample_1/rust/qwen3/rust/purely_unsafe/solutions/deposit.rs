use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

#[predicate]
pub account_pred(p: *mut Account) = 
    p != 0 &*& malloc_block_Account(p, 1) &*&
    *p |-> Account { balance: ?b } &*& 
    acc(p as int, b);

#[predicate]
pub acc(addr: int, value: int) = malloc_block((addr as *mut u8), 4) &*& * (addr as *mut i32) |-> value;

impl Account {
    unsafe fn create() -> *mut Account {
        #[requires(true)]
        #[ensures(account_pred(result))]
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        #[requires(my_account != 0 &*& malloc_block_Account(my_account, 1))]
        #[ensures(account_pred(my_account) &*& *my_account |-> Account { balance: 0 })]
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        #[requires(account_pred(my_account))]
        #[ensures(account_pred(my_account) &*& result == (*my_account).balance)]
        return (*my_account).balance;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        #[requires(account_pred(my_account))]
        #[ensures(account_pred(my_account) &*& (*my_account).balance == new_balance)]
        (*my_account).balance = new_balance;
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        #[requires(account_pred(my_account))]
        #[ensures(account_pred(my_account) &*& (*my_account).balance == old((*my_account).balance) + amount)]
        {
            let old_balance = (*my_account).balance;
            (*my_account).balance = old_balance + amount;
        }
    }

    unsafe fn dispose(my_account: *mut Account) {
        #[requires(account_pred(my_account))]
        #[ensures(true)]
        {
            close acc(my_account as int, (*my_account).balance);
            free(malloc_block_Account, my_account, 1);
            dealloc(my_account as *mut u8, Layout::new::<Account>());
        }
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