use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Account(balance: i32) = true;
@*/

struct Account {
    balance: i32,
}

impl Account {
    //@ req true;
    //@ ens alloc_block_account(result) &*& Account(0);
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account(0);
        (*my_account).balance = 0;
        return my_account;
    }

    //@ req alloc_block_account(my_account) &*& Account(balance);
    //@ ens alloc_block_account(my_account) &*& Account(balance) &*& result == balance;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    
    
    {
        //@ open Account(balance);
        let result = (*my_account).balance;
        //@ close Account(balance);
        return result;
    }

    //@ req alloc_block_account(my_account) &*& Account(_);
    //@ ens alloc_block_account(my_account) &*& Account(new_balance);
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
        //@ open Account(_);
        (*my_account).balance = new_balance;
        //@ close Account(new_balance);
    }

    //@ req alloc_block_account(my_account) &*& Account(old_balance);
    //@ ens alloc_block_account(my_account) &*& Account(old_balance + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    
    
    {
        //@ open Account(old_balance);
        (*my_account).balance += amount;
        //@ close Account(old_balance + amount);
    }

    //@ req alloc_block_account(my_account) &*& Account(_);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open Account(_);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main()

{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}