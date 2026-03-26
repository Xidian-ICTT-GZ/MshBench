use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

/*@
pred account(p: *mut Account;) =
    alloc_block(p as *mut u8, Layout::new_::<Account>()) &*&
    struct_Account_padding(p) &*&
    (*p).balance |-> _;
@*/

struct Account {
    balance: i32,
}

impl Account {
    #[unsafe_spec]
    #[requires(true)]
    #[ensures(account(result))]
    unsafe fn create() -> *mut Account {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close_struct(my_account);
        (*my_account).balance = 0;
        //@ close account(my_account);
        my_account
    }

    #[unsafe_spec]
    #[requires(account(my_account))]
    #[ensures(account(my_account))]
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32) {
        //@ open account(my_account);
        (*my_account).balance = new_balance;
        //@ close account(my_account);
    }

    #[unsafe_spec]
    #[requires(account(my_account))]
    #[ensures(true)]
    unsafe fn dispose(my_account: *mut Account) {
        //@ open account(my_account);
        //@ open_struct(my_account);
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