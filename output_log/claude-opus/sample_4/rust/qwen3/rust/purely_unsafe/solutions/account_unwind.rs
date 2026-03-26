use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred account_pred(p: *mut Account) = 
    p != 0 &*& 
    malloc_block_Account(p, sizeof<Account>()) &*&
    (*p).balance |-> _
]

#[lemma]
fn account_pred_split(p: *mut Account)
    requires account_pred(p),
    ensures account_pred(p)
{
    // lemma body can be empty, it's just for framing
}

struct Account {
    balance: i32,
}

impl Account {
    unsafe fn create() -> *mut Account {
        #[requires true]
        #[ensures account_pred(result) &*& (*result).balance |-> 0]
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        #[requires my_account != 0 &*& malloc_block_Account(my_account, sizeof<Account>())]
        #[ensures account_pred(my_account) &*& (*my_account).balance |-> 0]
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        #[requires account_pred(my_account)]
        #[ensures account_pred(my_account) &*& (*my_account).balance |-> newBalance]
        (*my_account).balance = newBalance;
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
        Account::dispose(my_account);
    }
}