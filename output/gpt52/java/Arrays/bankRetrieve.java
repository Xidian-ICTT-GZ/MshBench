class Account {
    int balance;

    /*@ predicate account(int b) = this.balance |-> b; @*/

    public Account()
    //@ requires true;
    //@ ensures account(0);
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate bank(Account[] a, int n, int cap) =
            this.store |-> a
        &*& this.nelems |-> n
        &*& this.capacity |-> cap
        &*& a != null
        &*& 0 < n
        &*& n <= cap
        &*& cap == a.length
        &*& a[n - 1] |-> ?last
        &*& last != null;
    @*/

    public Account retrieveLastAccount()
    //@ requires bank(?a, ?n, ?cap);
    //@ ensures this.store |-> a &*& this.nelems |-> (n - 1) &*& this.capacity |-> cap &*& a != null &*& n - 1 <= cap &*& cap == a.length &*& a[n - 1] |-> null &*& result != null;
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}