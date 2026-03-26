use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Account {
    balance: i32,
}

predicate acc(int *balance_ptr; int value) = balance_ptr |-> value;

predicate account_pred(Account *p) = 
    p != 0 &*& 
    malloc_block_Account(p, 1) &*& 
    p->balance |-> ?b &*& 
    acc(&(p->balance), b);

lemma void acc_read_write(int *balance_ptr, int old_value, int new_value)
    requires acc(balance_ptr, old_value);
    ensures acc(balance_ptr, new_value);
{
    open acc(balance_ptr, old_value);
    *balance_ptr = new_value;
    close acc(balance_ptr, new_value);
}

impl Account {
    unsafe fn create() -> *mut Account
    #[requires(true)]
    #[ensures(account_pred(result))]
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        (*my_account).balance = 0;
        close acc(&mut (*my_account).balance, 0);
        close account_pred(my_account);
        return my_account;
    }

    unsafe fn get_balance(my_account: *mut Account) -> i32
    #[requires(account_pred(my_account))]
    #[ensures(account_pred(my_account) &*& result == (*my_account).balance)]
    {
        open account_pred(my_account);
        open acc(&mut (*my_account).balance, _);
        int b = (*my_account).balance;
        close acc(&mut (*my_account).balance, b);
        close account_pred(my_account);
        return b;
    }

    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    #[requires(account_pred(my_account))]
    #[ensures(account_pred(my_account) &*& (*my_account).balance == new_balance)]
    {
        open account_pred(my_account);
        open acc(&mut (*my_account).balance, _);
        (*my_account).balance = new_balance;
        close acc(&mut (*my_account).balance, new_balance);
        close account_pred(my_account);
    }

    unsafe fn deposit(my_account: *mut Account, amount: i32)
    #[requires(account_pred(my_account))]
    #[ensures(account_pred(my_account) &*& (*my_account).balance == old((*my_account).balance) + amount)]
    {
        open account_pred(my_account);
        open acc(&mut (*my_account).balance, ?old_balance);
        int new_balance = old_balance + amount;
        (*my_account).balance = new_balance;
        close acc(&mut (*my_account).balance, new_balance);
        close account_pred(my_account);
    }

    unsafe fn dispose(my_account: *mut Account)
    #[requires(account_pred(my_account))]
    #[ensures(true)]
    {
        open account_pred(my_account);
        open acc(&mut (*my_account).balance, _);
        close acc(&mut (*my_account).balance, _); // Close again for balance
        dealloc(my_account as *mut u8, Layout::new::<Account>());
    }
}

fn main() {
    unsafe {
        let my_account = Account::create();
        Account::set_balance(my_account, 5);
        Account::deposit(my_account, 10);
        let b = Account::get_balance(my_account);
        std::hint::assert_unchecked(b == 15);
        Account::dispose(my_account);
    }
}