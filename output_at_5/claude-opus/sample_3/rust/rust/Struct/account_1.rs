use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
impl Account {
    unsafe fn create() -> *mut Account
        //@ requires true;
        //@ ensures malloc_block_account(result);
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        my_account
    }
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
        //@ requires malloc_block_account(my_account);
        //@ ensures malloc_block_account(my_account);
    {
        (*my_account).balance = new_balance;
    }
    unsafe fn dispose(my_account: *mut Account)
        //@ requires malloc_block_account(my_account);
        //@ ensures true;
    {
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}
//@ predicate malloc_block_account(void *p) = malloc_block(p, sizeof::<Account>()) &*& pointer(p, _);
fn main()
{
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::dispose(my_account);
    }
}