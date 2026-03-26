use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

/*@

pred Account(p: *mut Account; limit: i32, balance: i32) =
    p != 0 &*&
    (*p).limit |-> limit &*&
    (*p).balance |-> balance;

@*/

impl Account {

    unsafe fn create(limit: i32) -> *mut Account
    //@ req true;
    //@ ens result == 0 ? true : Account(result, limit, 0);
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        
        //@ close Account(my_account, limit, 0);
        my_account
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req Account(my_account, ?limit, ?balance);
    //@ ens Account(my_account, limit, balance) &*& result == balance;
    
    
    {
        
        //@ open Account(my_account, limit, balance);
        let result = (*my_account).balance;
        //@ close Account(my_account, limit, balance);
        
        result
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req Account(my_account, ?limit, ?balance);
    //@ ens Account(my_account, limit, balance + amount);
    
    
    {
        
        //@ open Account(my_account, limit, balance);
        (*my_account).balance += amount;
        //@ close Account(my_account, limit, balance + amount);
        
    }

    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32
    //@ req Account(my_account, ?limit, ?balance);
    //@ ens Account(my_account, limit, balance - result);
    
    

    {
        
        //@ open Account(my_account, limit, balance);
        let result =
            if (*my_account).balance - amount < (*my_account).limit {
                (*my_account).balance - (*my_account).limit
            } else {
                amount
            };
        (*my_account).balance -= result;
        //@ close Account(my_account, limit, balance - result);
        
        result
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req Account(my_account, ?limit, ?balance);
    //@ ens true;
    
    
    {
        
        //@ open Account(my_account, limit, balance);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main()

{
    unsafe {
        let my_account = Account::create(-100);
        //@ assert Account(my_account, -100, 0);
        Account::deposit(my_account, 200);
        //@ assert Account(my_account, -100, 200);
        let w1 = Account::withdraw(my_account, 50);
        //@ assert Account(my_account, -100, 200 - w1);
        std::hint::assert_unchecked(w1 == 50);
        //@ assert Account(my_account, -100, 150);
        let b1 = Account::get_balance(my_account);
        //@ assert Account(my_account, -100, 150);
        std::hint::assert_unchecked(b1 == 150);
        let w2 = Account::withdraw(my_account, 300);
        //@ assert Account(my_account, -100, 150 - w2);
        std::hint::assert_unchecked(w2 == 250);
        //@ assert Account(my_account, -100, -100);
        let b2 = Account::get_balance(my_account);
        //@ assert Account(my_account, -100, -100);
        std::hint::assert_unchecked(b2 == -100);
        Account::dispose(my_account);
    }
}