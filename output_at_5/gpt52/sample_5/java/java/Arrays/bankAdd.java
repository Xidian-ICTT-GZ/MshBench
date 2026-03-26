class Account {
    int balance;

    /*@
    predicate valid(Account a) = a.balance |-> ?b;
    @*/

    public Account()
    //@ requires balance |-> _;
    //@ ensures valid(this);
    {
        balance = 0;
        //@ close valid(this);
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate valid(Bank b) =
        b.capacity |-> ?cap &*&
        b.nelems |-> ?n &*&
        b.store |-> ?a &*&
        a != null &*& a.length == cap &*& 0 <= n &*& n <= cap;
    @*/

    public Bank(int cap)
    //@ requires capacity |-> _ &*& store |-> _ &*& nelems |-> _;
    //@ ensures valid(this);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close valid(this);
    }

    public void addNewAccount()
    //@ requires valid(this);
    //@ ensures valid(this);
    {
        //@ open valid(this);
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
        //@ close valid(this);
    }
}