class Account {
    int balance;

    /*@
    predicate valid() = balance |-> ?b;
    @*/

    public Account()
    //@ requires balance |-> _;
    //@ ensures valid();
    {
        balance = 0;
        //@ close valid();
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate valid() =
        capacity |-> ?cap &*&
        nelems |-> ?n &*&
        store |-> ?a &*&
        a != null &*& a.length == cap &*& 0 <= n &*& n <= cap;
    @*/

    public Bank(int cap)
    //@ requires capacity |-> _ &*& store |-> _ &*& nelems |-> _;
    //@ ensures valid();
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close valid();
    }

    public void addNewAccount()
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
        //@ close valid();
    }
}