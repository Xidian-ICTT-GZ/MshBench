use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

/*@
pred_ctor account_own(limit: i32, balance: i32)() = true;
pred Account(p: *mut Account; limit: i32, balance: i32) =
    alloc_block(p, std::mem::size_of::<Account>()) &*&
    struct_Account_fields(p, limit, balance) &*&
    account_own(limit, balance)();
@*/

/*@
pred struct_Account_fields(p: *mut Account, limit: i32, balance: i32) =
    (*p).limit |-> limit &*& (*p).balance |-> balance;
@*/

impl Account {
    //@ req true;
    //@ ens Account(result, limit, 0);
    unsafe fn create(limit: i32) -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close struct_Account_fields(my_account, _, _);
        //@ close account_own(limit, 0)();
        //@ close Account(my_account, limit, 0);
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        
        my_account
    }

    //@ req Account(my_account, limit, balance);
    //@ ens Account(my_account, limit, balance) &*& result == balance;
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        //@ open Account(my_account, limit, balance);
        //@ open struct_Account_fields(my_account, _, _);
        let result = (*my_account).balance;
        //@ close struct_Account_fields(my_account, limit, balance);
        //@ close Account(my_account, limit, balance);
        result
    }

    //@ req Account(my_account, limit, balance);
    //@ ens Account(my_account, limit, balance + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        //@ open Account(my_account, limit, balance);
        //@ open struct_Account_fields(my_account, _, _);
        (*my_account).balance += amount;
        //@ close struct_Account_fields(my_account, limit, balance + amount);
        //@ close Account(my_account, limit, balance + amount);
    }

    //@ req Account(my_account, limit, balance);
    //@ ens Account(my_account, limit, balance - result) &*& result == (if balance - amount < limit { balance - limit } else { amount });
    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32 {
        //@ open Account(my_account, limit, balance);
        //@ open struct_Account_fields(my_account, _, _);
        let result =
            if (*my_account).balance - amount < (*my_account).limit {
                (*my_account).balance - (*my_account).limit
            } else {
                amount
            };
        (*my_account).balance -= result;
        //@ close struct_Account_fields(my_account, limit, balance - result);
        //@ close Account(my_account, limit, balance - result);
        result
    }

    //@ req Account(my_account, limit, balance);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account) {
        //@ open Account(my_account, limit, balance);
        //@ open struct_Account_fields(my_account, _, _);
        //@ open account_own(limit, balance)();
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