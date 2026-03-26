use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

//@ predicate_unsafe account(struct Account *account; i32 limit, i32 balance) = account->limit |-> limit &*& account->balance |-> balance;

impl Account {

    unsafe fn create(limit: i32) -> *mut Account
    //@ req true;
    //@ ens account(result, limit, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close account(my_account, _, _);
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req account(my_account, ?limit, ?balance);
    //@ ens account(my_account, limit, balance) &*& result == balance;
    {
        //@ open account(my_account, _, _);
        return (*my_account).balance;
        //@ close account(my_account, _, _);
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req account(my_account, ?limit, ?balance);
    //@ ens account(my_account, limit, balance + amount);
    {
        //@ open account(my_account, _, _);
        (*my_account).balance += amount;
        //@ close account(my_account, _, _);
    }

    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32
    //@ req account(my_account, ?limit, ?balance);
    //@ ens account(my_account, limit, balance - result) &*& result == (if balance - amount < limit { balance - limit } else { amount });
    {
        //@ open account(my_account, _, _);
        let result = if (*my_account).balance - amount < (*my_account).limit { (*my_account).balance - (*my_account).limit } else { amount };
        (*my_account).balance -= result;
        //@ close account(my_account, _, _);
        return result;
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req account(my_account, _, _);
    //@ ens true;
    {
        //@ open account(my_account, _, _);
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