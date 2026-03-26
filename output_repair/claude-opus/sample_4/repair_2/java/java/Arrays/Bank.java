class Account {
    int balance;

    //@ ensures this.balance |-> 0;
    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate valid() =
        this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*&
        0 <= n &*& n <= c &*& s != null &*& array_slice(s, 0, c, _);
    @*/

    //@ requires cap > 0;
    //@ ensures this.store |-> _ &*& this.nelems |-> 0 &*& this.capacity |-> cap &*& array_slice(this.store, 0, cap, _);
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& 0 <= n &*& n < c &*& s != null &*& array_slice(s, 0, c, _);
    //@ ensures this.store |-> ?s &*& this.nelems |-> (n + 1) &*& this.capacity |-> ?c &*& s != null &*& array_slice(s, 0, c, _);
    public void addNewAccount()
    {
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
    }
}