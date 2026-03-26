class Account {
    int balance;

    /*@ predicate valid(Account this) = this.balance |-> ?b; @*/

    //@ requires true
    //@ ensures valid(this)
    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate valid(Bank this) =
        this.store |-> ?s &*&
        this.nelems |-> ?n &*&
        this.capacity |-> ?c &*&
        0 <= n &*& n <= c &*&
        s != null &*&
        array_slice(s, 0, n, _); @*/

    //@ requires cap > 0
    //@ ensures valid(this)
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires valid(this) &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& n < c
    //@ ensures valid(this) &*& this.nelems |-> (n + 1)
    public void addNewAccount()
    {
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
    }
}