use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

/*@

predicate account(p: *mut Account; bal: i32) =
    std::alloc::alloc_block(p as *mut u8, Layout::new::<Account>()) &*&
    struct_Account(p, bal);

@*/

impl Account {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut::<Account>() &*& account(result, 0))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close struct_Account(my_account, _);
        (*my_account).balance = 0;
        //@ close account(my_account, 0);
        my_account
    }

    #[requires(account(my_account, _))]
    #[ensures(account(my_account, new_balance))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        //@ open account(my_account, _);
        //@ open struct_Account(my_account, _);
        (*my_account).balance = new_balance;
        //@ close struct_Account(my_account, new_balance);
        //@ close account(my_account, new_balance);
    }

    #[requires(account(my_account, _))]
    #[ensures(true)]
    unsafe fn dispose(my_account: *mut Account) {
        //@ open account(my_account, _);
        //@ open struct_Account(my_account, _);
        //@ open std::alloc::alloc_block(my_account as *mut u8, Layout::new::<Account>());
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}