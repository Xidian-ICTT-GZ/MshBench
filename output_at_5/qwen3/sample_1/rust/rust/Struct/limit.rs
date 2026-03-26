use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    limit: i32,
    balance: i32,
}

// Predicate to represent a valid account memory location
pred account(ptr: *mut Account, lim: i32, bal: i32) = 
    ptr != null() && 
    (*ptr).limit == lim && 
    (*ptr).balance == bal;

impl Account {

    unsafe fn create(limit: i32) -> *mut Account
    //@ requires true;
    //@ ensures result != null() && account(result, limit, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        // Initialize the memory so the predicate holds
        (*my_account).limit = limit;
        (*my_account).balance = 0;
        my_account
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ requires account(my_account, _, _);
    //@ ensures ens(account(my_account, _, ret));
    {
        // Open the predicate to read fields
        open account(my_account, _, _);
        let res = (*my_account).balance;
        close account(my_account, _, _);
        res
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ requires account(my_account, lim, bal);
    //@ ensures account(my_account, lim, bal + amount);
    {
        open account(my_account, lim, bal);
        (*my_account).balance += amount;
        close account(my_account, lim, bal + amount);
    }

    unsafe fn withdraw(my_account: *mut Account, amount: i32) -> i32
    //@ requires account(my_account, lim, bal);
    //@ ensures account(my_account, lim, bal - ret) && (ret <= amount) && (bal - ret >= lim);
    {
        open account(my_account, lim, bal);
        
        // Logic extraction for verification
        let new_bal = if bal - amount < lim {
            lim
        } else {
            bal - amount
        };
        
        // Calculate result based on logic
        let result = bal - new_bal;
        
        (*my_account).balance = new_bal;
        
        close account(my_account, lim, new_bal);
        result
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ requires account(my_account, _, _);
    //@ ensures true;
    {
        open account(my_account, _, _);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
        // After dealloc, the pointer is no longer valid, but we ensure the contract held before
    }

}

fn main() {
    unsafe {
        let my_account = Account::create(-100);
        // Verify initial state
        open account(my_account, -100, 0);
        close account(my_account, -100, 0);
        
        Account::deposit(my_account, 200);
        // State after deposit: limit=-100, balance=200
        open account(my_account, -100, 200);
        close account(my_account, -100, 200);
        
        let w1 = Account::withdraw(my_account, 50);
        // verify w1 == 50
        assert(w1 == 50);
        // State after withdraw: limit=-100, balance=150
        open account(my_account, -100, 150);
        close account(my_account, -100, 150);
        
        let b1 = Account::get_balance(my_account);
        assert(b1 == 150);
        
        let w2 = Account::withdraw(my_account, 300);
        // verify w2 == 250 (since 150 - 300 = -150 < -100, result is 150 - (-100) = 250)
        assert(w2 == 250);
        // State after withdraw: limit=-100, balance=-100
        open account(my_account, -100, -100);
        close account(my_account, -100, -100);
        
        let b2 = Account::get_balance(my_account);
        assert(b2 == -100);
        
        Account::dispose(my_account);
    }
}