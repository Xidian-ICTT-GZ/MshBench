/*@ pred account(t: *mut Account, b: i32) = 
    alloc_block(t, std::mem::size_of::<Account>()) &*& 
    struct_Account_padding(t) &*& 
    (*t).balance |-> b;
@*/

/*@ pred struct_Account_padding(t: *mut Account) = true; @*/

impl Account {

    //@ req true;
    //@ ens account(result, 0);
    unsafe fn create() -> *mut Account
    
    
    {
        let my_account = alloc(Layout::new::<Account>()) as *mut Account;
        if my_account.is_null() {
            handle_alloc_error(Layout::new::<Account>());
        }
        //@ close struct_Account_padding(my_account);
        //@ close account(my_account, 0);
        (*my_account).balance = 0;
        return my_account;
    }

    //@ req account(my_account, ?b);
    //@ ens account(my_account, b) &*& result == b;
    unsafe fn get_balance(my_account: *mut Account) -> i32
    
    
    {
        //@ open account(my_account, _);
        let b = (*my_account).balance;
        //@ close account(my_account, b);
        return b;
    }

    //@ req account(my_account, ?old_b);
    //@ ens account(my_account, new_balance);
    unsafe fn set_balance(my_account: *mut Account, new_balance: i32)
    
    
    {
        //@ open account(my_account, _);
        (*my_account).balance = new_balance;
        //@ close account(my_account, new_balance);
    }

    //@ req account(my_account, ?old_b);
    //@ ens account(my_account, old_b + amount);
    unsafe fn deposit(my_account: *mut Account, amount: i32)
    
    
    {
        //@ open account(my_account, ?b);
        (*my_account).balance += amount;
        //@ close account(my_account, b + amount);
    }

    //@ req account(my_account, ?b);
    //@ ens true;
    unsafe fn dispose(my_account: *mut Account)
    
    
    {
        //@ open account(my_account, _);
        //@ open struct_Account_padding(my_account);
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