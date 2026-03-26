class Account {
    int balance;

    //@ requires emp;
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

    //@ requires this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& n > 0 &*& n <= s.length;
    //@ ensures this.store |-> ?s &*& this.nelems |-> (n - 1) &*& this.capacity |-> ?c &*& result != null;
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}