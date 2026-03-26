use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred Account_inv(p: *mut Account; limit: i32; balance: i32) =
    alloc_block(p as *u8, Layout::new_::<Account>()) &*&
    (*p).limit |-> limit &*&
    (*p).balance |-> balance;

@*/

struct Account {
    limit: i32,
    balance: i32,
}

impl Account {

    //@ req true;
    //@ ens result != std::ptr::null_mut() ==> Account_inv(result, limit, 0);
    unsafe fn create(limit: i32) -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ assume(my_account != std::ptr::null_mut());
        //@ close Account_inv(my_account, limit, 0);
        //@ open Account_inv(my_account, limit, 0);
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        //@ close Account_inv(my_account, limit, 0);
        return my_account;
    }

    //@ req Account_inv(my_account, ?limit, ?balance);
    //@ ens Account_inv(my_account, limit, balance) &*& result == balance;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    
    
    
    {
        //@ open Account_inv(my_account, ?limit, ?balance);
        let res = (*my_account).balance;
        //@ close Account_inv(my_account, limit, balance);
        return res;
    }

    //@ req Account_inv(my_account, ?limit, ?balance);
    //@ ens Account_inv(my_account, limit, balance + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    
    
    
    {
        //@ open Account_inv(my_account, ?limit, ?balance);
        (*my_account).balance += amount;
        //@ close Account_inv(my_account, limit, balance + amount);
    }

    //@ req Account_inv(my_account, ?limit, ?balance);
    //@ ens Account_inv(my_account, limit, balance - result);
    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32
    
    
    
    {
        //@ open Account_inv(my_account, ?limit, ?balance);
        let result = if (*my_account).balance - amount < (*my_account).limit { (*my_account).balance - (*my_account).limit } else { amount };
        (*my_account).balance -= result;
        //@ close Account_inv(my_account, limit, balance - result);
        return result;
    }

    //@ req Account_inv(my_account, ?limit, ?balance);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open Account_inv(my_account, limit, balance);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let my_account = Account::create(-100);
        //@ open Account_inv(my_account, ?limit0, ?balance0);
        //@ close Account_inv(my_account, limit0, balance0);
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