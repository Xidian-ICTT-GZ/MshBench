use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
struct Account {
    balance: i32,
}
//@ pred account(p: *mut Account, balance: i32) = p as *mut u8 |-> ?b &*& struct_Account_padding(?padding) &*& [?q]std::alloc::Global().alloc_block(p as *mut u8, Layout::new::<Account>(), q) &*& (*p).balance |-> balance;
impl Account {
unsafe fn create() -> *mut Account
//@ req true;
//@ ens account(result, 0);
{
    let my_account = alloc(Layout::new::<Account>()) as *mut Account;
    if my_account.is_null() {
        handle_alloc_error(Layout::new::<Account>());
    }
    //@ close account(my_account, 0);
    (*my_account).balance = 0;
    my_account
}
unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
//@ req account(my_account, _);
//@ ens account(my_account, new_balance);
{
    //@ open account(my_account, _);
    (*my_account).balance = new_balance;
    //@ close account(my_account, new_balance);
}
unsafe fn dispose(my_account: *mut Account)
//@ req account(my_account, _);
//@ ens true;
{
    //@ open account(my_account, _);
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
    Account::dispose(my_account);
    }
}