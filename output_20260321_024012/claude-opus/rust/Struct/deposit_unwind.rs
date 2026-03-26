use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    unsafe fn create() -> *mut Account
    //@ requires true;
    //@ ensures res != std::ptr::null_mut::<Account>() && acc(self, res);
    {
        /*@
        pred acc(Account *a) = malloc_block(a, sizeof(Account)) &*& *a->balance |-> ?bal;
        @*/
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ requires acc(my_account);
    //@ ensures acc(my_account) &*& result == (*my_account).balance;
    {
        return (*my_account).balance;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ requires acc(my_account);
    //@ ensures acc(my_account) &*& (*my_account).balance == new_balance;
    {
        (*my_account).balance = new_balance;
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ requires acc(my_account);
    //@ ensures acc(my_account) &*& (*my_account).balance == old((*my_account).balance) + amount; 
    {
        (*my_account).balance += amount;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ requires acc(my_account);
    //@ ensures true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

//@ predicate acc(Account *acc_ptr) = malloc_block(acc_ptr, sizeof(Account)) &*& *acc_ptr->balance |-> _;

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