class Account {
    int balance;

    /*@
    predicate inv() = this.balance |-> _;
    @*/

    public Account()
    //@ requires true;
    //@ ensures inv();
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate inv() = 
        this.store |-> ?s &*&
        this.nelems |-> ?n &*&
        this.capacity |-> ?c &*&
        s != null &*& n >= 0 &*& n <= c &*&
        array(store, c, ?accounts);
    @*/

    //@ predicate array(Account[] a, int len, list<Account> accounts) = a != null &*& a.length == len &*& true;

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures inv();
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires inv() &*& nelems < capacity;
    //@ ensures inv() &*& nelems == old(nelems) + 1;
    {
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
    }
}