use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ requires true;
    //@ ensures result != 0 &*& account(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        //@ close account(my_account, 0);
        my_account
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ requires account(my_account, _);
    //@ ensures account(my_account, new_balance);
    {
        //@ open account(my_account, _);
        (*my_account).balance = new_balance;
        //@ close account(my_account, new_balance);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ requires account(my_account, _);
    //@ ensures true;
    {
        //@ open account(my_account, _);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

/*@
predicate account(Account* a, int balance) = a->balance |-> balance;
@*/

fn main()
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}