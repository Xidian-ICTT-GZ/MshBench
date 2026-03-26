class Account {
    int balance;

    //@ predicate valid() = this.balance |-> ?b;

    public Account()
    //@ requires this.balance |-> _;
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
        this.capacity |-> ?cap &*&
        this.nelems |-> ?n &*&
        this.store |-> ?a &*&
        a != null &*& a.length == cap &*& 0 <= n &*& n <= cap;
    @*/

    public Bank(int cap)
    //@ requires this.capacity |-> _ &*& this.store |-> _ &*& this.nelems |-> _;
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
        //@ open c.valid();
        store[nelems] = c;
        
        nelems = nelems + 1;
        //@ close valid();
    }
}