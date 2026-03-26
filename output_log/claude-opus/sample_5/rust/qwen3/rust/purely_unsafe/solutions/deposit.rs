use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Account {
    balance: i32,
}

#[predicate]
pub account_pred(p: *mut Account) =
    p != 0 &*& malloc_block_Account(p, 1) &*& acc_balance_field(p, ?b) &*& *p |-> Account { balance: b };

#[predicate]
pub acc_balance_field(p: *mut Account, b: i32) =
    p != 0 &*& *p |-> Account { balance: b };

#[lemma]
fn account_balance_access(p: *mut Account)
    requires account_pred(p)
    ensures account_pred(p) &*& exists(?b) &*& acc_balance_field(p, b)
{
    open account_pred(p);
    close account_pred(p);
}

impl Account {
    unsafe fn create() -> *mut Account {
        #[requires(true)]
        #[ensures(account_pred(result))]
        {
            let my_account = alloc(Layout::new::<Account>()) as *mut Account;
            if my_account.is_null() {
                handle_alloc_error(Layout::new::<Account>());
            }
            #[invariant(malloc_block_Account(my_account, 1))]
            {
                *my_account = Account { balance: 0 };
            }
            close account_pred(my_account);
            my_account
        }
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        #[requires(account_pred(my_account))]
        #[ensures(account_pred(my_account) &*& result == (*my_account).balance)]
        {
            open account_pred(my_account);
            let b = (*my_account).balance;
            close account_pred(my_account);
            b
        }
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        #[requires(account_pred(my_account))]
        #[ensures(account_pred(my_account) &*& (*my_account).balance == new_balance)]
        {
            open account_pred(my_account);
            *my_account = Account { balance: new_balance };
            close account_pred(my_account);
        }
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        #[requires(account_pred(my_account))]
        #[ensures(account_pred(my_account) &*& (*my_account).balance == old((*my_account).balance) + amount)]
        {
            open account_pred(my_account);
            let old_balance = (*my_account).balance;
            *my_account = Account { balance: old_balance + amount };
            close account_pred(my_account);
        }
    }

    unsafe fn dispose(my_account: *mut Account) {
        #[requires(account_pred(my_account))]
        #[ensures(true)]
        {
            open account_pred(my_account);
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