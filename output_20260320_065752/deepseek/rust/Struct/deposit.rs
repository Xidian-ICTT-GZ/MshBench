use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

/*@
pred_ctor Account_own(account: *mut Account, balance: i32)() = 
    struct_Account { balance }@account;
@*/

impl Account {
    //@ req true;
    //@ ens Account_own(result, 0)();
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close Account_own(my_account, 0)();
        (*my_account).balance = 0;
        return my_account;
    }

    //@ req Account_own(my_account, ?balance)();
    //@ ens Account_own(my_account, balance)() &*& result == balance;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    
    
    {
        //@ open Account_own(my_account, ?balance)();
        let result = (*my_account).balance;
        //@ close Account_own(my_account, balance)();
        return result;
    }

    //@ req Account_own(my_account, _)();
    //@ ens Account_own(my_account, new_balance)();
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
        //@ open Account_own(my_account, _)();
        (*my_account).balance = new_balance;
        //@ close Account_own(my_account, new_balance)();
    }

    //@ req Account_own(my_account, ?balance)();
    //@ ens Account_own(my_account, balance + amount)();
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    
    
    {
        //@ open Account_own(my_account, ?balance)();
        (*my_account).balance += amount;
        //@ close Account_own(my_account, balance + amount)();
    }

    //@ req Account_own(my_account, _)();
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open Account_own(my_account, _)();
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