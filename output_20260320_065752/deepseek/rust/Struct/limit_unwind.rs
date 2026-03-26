use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Account(limit: i32, balance: i32) = true;
@*/

struct Account {
    limit: i32,
    balance: i32,
}

impl Account {
    //@ req true;
    //@ ens alloc_block_account(result) &*& Account(limit, 0)@result;
    unsafe fn create(limit: i32) -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        return my_account;
    }

    //@ req alloc_block_account(my_account) &*& Account(limit, balance)@my_account;
    //@ ens alloc_block_account(my_account) &*& Account(limit, balance)@my_account &*& result == balance;
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        return (*my_account).balance;
    }

    //@ req alloc_block_account(my_account) &*& Account(limit, old_balance)@my_account;
    //@ ens alloc_block_account(my_account) &*& Account(limit, old_balance + amount)@my_account;
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        (*my_account).balance += amount;
    }

    //@ req alloc_block_account(my_account) &*& Account(limit, old_balance)@my_account;
    //@ ens alloc_block_account(my_account) &*& Account(limit, old_balance - result)@my_account &*& result == (if old_balance - amount < limit { old_balance - limit } else { amount });
    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32 {
        let result = if (*my_account).balance - amount < (*my_account).limit { (*my_account).balance - (*my_account).limit } else { amount };
        (*my_account).balance -= result;
        return result;
    }

    //@ req alloc_block_account(my_account) &*& Account(_, _)@my_account;
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account) {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    unsafe {
        let my_account = Account::create(-100);
        //@ open Account(-100, 0)@my_account;
        //@ close Account(-100, 0)@my_account;
        Account::deposit(my_account, 200);
        //@ open Account(-100, 200)@my_account;
        //@ close Account(-100, 200)@my_account;
        let w1 = Account::withdraw(my_account, 50);
        //@ assert w1 == 50;
        std::hint::assert_unchecked(w1 == 50);
        let b1 = Account::get_balance(my_account);
        //@ assert b1 == 150;
        std::hint::assert_unchecked(b1 == 150);
        let w2 = Account::withdraw(my_account, 300);
        //@ assert w2 == 250;
        std::hint::assert_unchecked(w2 == 250);
        let b2 = Account::get_balance(my_account);
        //@ assert b2 == -100;
        std::hint::assert_unchecked(b2 == -100);
        Account::dispose(my_account);
    }
}