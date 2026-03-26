use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

/*@
predicate account_owned(ptr: *mut Account) =
    ptr as usize != 0 &*&
    std::alloc::alloc_block(Layout::new::<Account>(), ptr as *mut u8) &*&
    (*ptr).balance |-> _;
@*/

impl Account {
    /*@
    requires true;
    ensures account_owned(result);
    @*/
    unsafe fn create() -> *mut Account {
        let layout = Layout::new::<Account>();
        let my_account = alloc(layout) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(layout);
        }
        (*my_account).balance = 0;
        return my_account;
    }

    /*@
    requires account_owned(my_account);
    ensures account_owned(my_account);
    @*/
    unsafe fn set_balance(my_account: *mut Account, newBalance: i32) {
        (*my_account).balance = newBalance;
    }

    /*@
    requires account_owned(my_account);
    ensures true;
    @*/
    unsafe fn dispose(my_account: *mut Account) {
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