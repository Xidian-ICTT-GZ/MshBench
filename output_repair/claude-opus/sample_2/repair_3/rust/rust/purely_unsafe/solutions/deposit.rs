use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

/*@
pred account_owns(account: *mut Account; balance: i32) =
    (*account).balance |-> balance &*& struct_Account_padding(account) &*& alloc_block(account as *mut u8, Layout::new::<Account>());
@*/

impl Account {
    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ens account_owns(result, 0);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close_struct(my_account);
        (*my_account).balance = 0;
        //@ close account_owns(my_account, 0);
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req account_owns(my_account, ?balance);
    //@ ens account_owns(my_account, balance) &*& result == balance;
    {
        //@ open account_owns(my_account, balance);
        let result = (*my_account).balance;
        //@ close account_owns(my_account, balance);
        return result;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req account_owns(my_account, _);
    //@ ens account_owns(my_account, new_balance);
    {
        //@ open account_owns(my_account, _);
        (*my_account).balance = new_balance;
        //@ close account_owns(my_account, new_balance);
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req account_owns(my_account, ?balance);
    //@ ens account_owns(my_account, balance + amount);
    {
        //@ open account_owns(my_account, balance);
        (*my_account).balance += amount;
        //@ close account_owns(my_account, balance + amount);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req account_owns(my_account, _);
    //@ ens true;
    {
        //@ open account_owns(my_account, _);
        //@ open_struct(my_account);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main()
//@ req true;
//@ ens true;
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