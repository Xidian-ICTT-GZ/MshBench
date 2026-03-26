use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

/*@
pred Account_own(p: *mut Account, bal: i32) = 
    (*p).balance |-> bal;
@*/

impl Account {
    #[unsafe_block_pre(Layout::new_::<Account>())]
    #[ensures(Account_own(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ open_struct(my_account);
        (*my_account).balance = 0;
        return my_account;
    }

    #[requires(Account_own(my_account, bal))]
    #[ensures(Account_own(my_account, bal) &*& result == bal)]
    unsafe fn get_balance(my_account: *mut Account) -> i32 {
        //@ open Account_own(my_account, bal);
        let result = (*my_account).balance;
        //@ close Account_own(my_account, bal);
        return result;
    }

    #[requires(Account_own(my_account, _))]
    #[ensures(Account_own(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        //@ open Account_own(my_account, _);
        (*my_account).balance = new_balance;
        //@ close Account_own(my_account, new_balance);
    }

    #[requires(Account_own(my_account, old_bal))]
    #[ensures(Account_own(my_account, old_bal + amount))]
    unsafe fn deposit(my_account: *mut Account, amount: i32) {
        //@ open Account_own(my_account, old_bal);
        (*my_account).balance += amount;
        //@ close Account_own(my_account, old_bal + amount);
    }

    #[unsafe_block_pre(Layout::new_::<Account>() &*& Account_own(my_account, _))]
    #[requires(Account_own(my_account, _))]
    unsafe fn dispose(my_account: *mut Account) {
        //@ open Account_own(my_account, _);
        //@ close_struct(my_account);
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    unsafe {
        //@ Layout::new_::<Account>();
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}