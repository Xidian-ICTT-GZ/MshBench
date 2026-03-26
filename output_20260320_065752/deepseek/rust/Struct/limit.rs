use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

/*@
pred_ctor Account_own(account: *mut Account, limit: i32, balance: i32)() =
    alloc_block(account, std::mem::size_of::<Account>()) &*&
    struct_Account_padding(account) &*&
    (*account).limit |-> limit &*&
    (*account).balance |-> balance;
@*/

impl Account {

    unsafe fn create(limit: i32) -> *mut Account
    //@ req true;
    //@ ens Account_own(result, limit, 0)();
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account_own(my_account, limit, 0)();
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        my_account
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req Account_own(my_account, ?limit, ?balance)();
    //@ ens Account_own(my_account, limit, balance)() &*& result == balance;
    
    
    {
        //@ open Account_own(my_account, ?limit, ?balance)();
        let result = (*my_account).balance;
        //@ close Account_own(my_account, limit, balance)();
        result
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req Account_own(my_account, ?limit, ?balance)();
    //@ ens Account_own(my_account, limit, balance + amount)();
    
    
    {
        //@ open Account_own(my_account, ?limit, ?balance)();
        (*my_account).balance += amount;
        //@ close Account_own(my_account, limit, balance + amount)();
    }

    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32
    //@ req Account_own(my_account, ?limit, ?balance)();
    /*@ ens Account_own(my_account, limit, balance - result)() &*&
        result == (if balance - amount < limit { balance - limit } else { amount });
    @*/
    
    

    {
        //@ open Account_own(my_account, ?limit, ?balance)();
        let result =
            if (*my_account).balance - amount < (*my_account).limit {
                (*my_account).balance - (*my_account).limit
            } else {
                amount
            };
        (*my_account).balance -= result;
        //@ close Account_own(my_account, limit, balance - result)();
        result
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account_own(my_account, _, _)();
    //@ ens true;
    
    
    {
        //@ open Account_own(my_account, _, _)();
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