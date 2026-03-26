use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Account_balance(p: *mut Account; v: i32) = (*p).balance |-> v;

pred Account_full(p: *mut Account; v: i32) =
    alloc_block_Account(p) &*& struct_Account_padding(p) &*& Account_balance(p, v);
@*/

struct Account {
    balance: i32,
}

impl Account {

    //@ req true;
    //@ ens Account_full(result, 0);
    unsafe fn create() -> *mut Account
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close_struct_Account(my_account);
        (*my_account).balance = 0;
        //@ close Account_balance(my_account, 0);
        //@ close Account_full(my_account, 0);
        return my_account;
    }

    //@ req Account_full(my_account, _);
    //@ ens Account_full(my_account, newBalance);
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    {
        //@ open Account_full(my_account, _);
        //@ open Account_balance(my_account, _);
        (*my_account).balance = newBalance;
        //@ close Account_balance(my_account, newBalance);
        //@ close Account_full(my_account, newBalance);
    }

    //@ req Account_full(my_account, _);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    {
        //@ open Account_full(my_account, _);
        //@ open Account_balance(my_account, _);
        //@ open_struct_Account(my_account);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }

}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}