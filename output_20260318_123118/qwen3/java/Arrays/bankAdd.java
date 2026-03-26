/*@ predicate account(Account a; int bal) =
    a |-> balance |-> bal;
@*/

/*@ predicate bank(Bank b; Account[] store; int nelems, int capacity) =
    b |-> store |-> store &*&
    b |-> nelems |-> nelems &*&
    b |-> capacity |-> capacity &*&
    0 <= nelems &*& nelems <= capacity &*&
    array_slice(store, 0, nelems, ?accounts) &*&
    foreach(accounts, account_pred);
@*/

/*@ predicate account_pred(Account a) = account(a, _); @*/

class Account {
    int balance;

    //@ requires true;
    //@ ensures account(this, 0);
    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ requires 0 <= cap;
    //@ ensures bank(this, result_, nelems_, capacity_) &*& result_ == this &*& nelems_ == 0 &*& capacity_ == cap;
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires bank(this, ?store0, ?nelems0, ?capacity0) &*& nelems0 < capacity0;
    //@ ensures bank(this, ?store1, ?nelems1, ?capacity1) &*& nelems1 == nelems0 + 1 &*& capacity1 == capacity0;
    public void addNewAccount()
    {
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
    }
}