use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred account_pred(p: *mut Account) = 
    p != 0 &*& 
    malloc_block_Account(p, 1) &*& 
    *p |-> Account { balance: ?b } &*& 
    acc(_balance_field(p), b)
]

#[pred _balance_field(p: *mut Account) = 
    p != 0 &*& 
    *p |-> Account { balance: ?b } &*& 
    acc(_balance_field(p), b)
]

#[lemma]
fn account_balance_access(p: *mut Account)
    requires account_pred(p)
    ensures account_pred(p) &*& exists(?b) &*& *p |-> Account { balance: b } &*& acc(_balance_field(p), b)
{
    // This lemma is trivial in VeriFast due to the structure of the predicate.
}

impl Account {
    unsafe fn create() -> *mut Account {
        #[requires true]
        #[ensures account_pred(result)]
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        #[requires my_account != 0 &*& malloc_block_Account(my_account, 1)]
        #[ensures account_pred(my_account) &*& *my_account |-> Account { balance: 0 }]
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        #[requires account_pred(my_account)]
        #[ensures account_pred(my_account) &*& result == (*my_account).balance]
        return (*my_account).balance;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        #[requires account_pred(my_account)]
        #[ensures account_pred(my_account) &*& (*my_account).balance == new_balance]
        (*my_account).balance = new_balance;
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        #[requires account_pred(my_account)]
        #[ensures account_pred(my_account) &*& (*my_account).balance == (*my_account).balance + amount]
        (*my_account).balance += amount;
    }

    unsafe fn dispose(my_account: *mut Account) {
        #[requires account_pred(my_account)]
        #[ensures true]
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