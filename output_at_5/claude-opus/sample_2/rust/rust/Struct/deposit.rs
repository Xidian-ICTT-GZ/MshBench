use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Account {
    balance: i32,
}

impl Account {

    /*@ 
    predicate valid_account(Account* p) = p |-> Account {balance: _};
    @*/

    unsafe fn create() -> *mut Account
    //@ req true;
    //@ ensures valid_account(result);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        //@ close valid_account(my_account);
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    //@ req valid_account(my_account);
    //@ ensures valid_account(my_account) &*& result == (*my_account).balance;
    {
        //@ open valid_account(my_account);
        let bal = (*my_account).balance;
        //@ close valid_account(my_account);
        return bal;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    //@ req valid_account(my_account);
    //@ ensures valid_account(my_account) &*& (*my_account).balance == new_balance;
    {
        //@ open valid_account(my_account);
        (*my_account).balance = new_balance;
        //@ close valid_account(my_account);
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    //@ req valid_account(my_account);
    //@ ensures valid_account(my_account) &*& (*my_account).balance == old((*my_account).balance) + amount;
    {
        //@ open valid_account(my_account);
        (*my_account).balance += amount;
        //@ close valid_account(my_account);
    }

    unsafe fn dispose(my_account: *mut Account)
    //@ req valid_account(my_account);
    //@ ensures true;
    {
        //@ open valid_account(my_account);
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