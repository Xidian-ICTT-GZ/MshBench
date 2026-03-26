use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens result != 0;
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req my_account != 0 &*& my_account->balance(_, _);
    //@ ens my_account->balance(_, _);
    {
        (*my_account).balance = new_balance;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req my_account != 0 &*& my_account->balance(_, _);
    //@ ens true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

// Define a predicate for the fields of Account struct
/*@
predicate account(struct Account *a; int balance) = a->balance |-> balance;
@*/

fn main()
{
    unsafe {
        let my_account = Account::create();
        //@ open account(my_account, _);
        Account::set_balance(my_account, 5);
        //@ close account(my_account, 5);
        Account::dispose(my_account);
    }
}