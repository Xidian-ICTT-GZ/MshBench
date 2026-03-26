use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate Account_own(*mut Account acc; i32 balance) =
    acc |-> struct_Account { balance: balance };

struct Account {
    balance: i32,
}

impl Account {

    #[requires(true)]
    #[ensures(Account_own(result, 0))]
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(Account_own(my_account, _))]
    #[ensures(Account_own(my_account, newBalance))]
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32)
    
    
    
    {
        (*my_account).balance = newBalance;
    }

    #[requires(Account_own(my_account, _))]
    #[ensures(true)]
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
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