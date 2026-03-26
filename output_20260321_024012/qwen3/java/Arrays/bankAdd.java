/*@ 
predicate account(Account a; int balance) = a.balance |-> balance;
predicate bank(Bank b; Account[] store, int nelems, int capacity) =
    b.store |-> store &*& b.nelems |-> nelems &*& b.capacity |-> capacity &*&
    0 <= nelems &*& nelems <= capacity &*&
    array_slice(store, 0, nelems, ?accounts) &*&
    foreach(accounts, account_pred);
predicate account_pred(Account a) = account(a, _);
@*/

class Account {
    int balance;

    //@ requires true;
    //@ ensures account(this, 0);
    public Account()
    {
        balance = 0;
        //@ close account(this, 0);
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ requires 0 <= cap;
    //@ ensures bank(this, ?store, 0, cap) &*& length(store) == cap;
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close bank(this, store, 0, cap);
    }

    //@ requires bank(this, ?store0, ?nelems0, ?cap) &*& nelems0 < cap;
    //@ ensures bank(this, ?store1, nelems0 + 1, cap) &*& length(store1) == cap;
    public void addNewAccount()
    {
        //@ open bank(this, store0, nelems0, cap);
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
        //@ close bank(this, store0, nelems0 + 1, cap);
    }
}