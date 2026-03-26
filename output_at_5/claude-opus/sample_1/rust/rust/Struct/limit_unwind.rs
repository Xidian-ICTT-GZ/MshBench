use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

impl Account {

    //@ predicate account_pred(Account *acct;) = acct->limit |-> _ &*& acct->balance |-> _;
    
    unsafe fn create(limit: i32) -> *mut Account
    //@ requires true;
    //@ ensures account_pred(result);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        //@ close account_pred(my_account);
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ requires account_pred(my_account);
    //@ ensures account_pred(my_account);
    {
        //@ open account_pred(my_account);
        let res = (*my_account).balance;
        //@ close account_pred(my_account);
        return res;
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ requires account_pred(my_account);
    //@ ensures account_pred(my_account);
    {
        //@ open account_pred(my_account);
        (*my_account).balance += amount;
        //@ close account_pred(my_account);
    }

    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32
    //@ requires account_pred(my_account);
    //@ ensures account_pred(my_account);
    {
        //@ open account_pred(my_account);
        let bal = (*my_account).balance;
        let lim = (*my_account).limit;
        let result = if bal - amount < lim { bal - lim } else { amount };
        (*my_account).balance -= result;
        //@ close account_pred(my_account);
        return result;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ requires account_pred(my_account);
    //@ ensures true;
    {
        //@ open account_pred(my_account);
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