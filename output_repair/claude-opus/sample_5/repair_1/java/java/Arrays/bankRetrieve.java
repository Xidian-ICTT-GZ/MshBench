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

    //@ requires this.store |-> _ &*& this.nelems |-> ?n &*& this.capacity |-> _ &*& n > 0 &*& n <= store.length;
    //@ ensures this.store |-> _ &*& this.nelems |-> (n - 1) &*& this.capacity |-> _ &*& result != null;
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}