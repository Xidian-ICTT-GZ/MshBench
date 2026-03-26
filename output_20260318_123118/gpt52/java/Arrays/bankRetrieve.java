class Account {
    int balance;

    /*@ predicate account_inv() = this.balance |-> ?b; @*/

    public Account()
    //@ requires this.balance |-> _;
    //@ ensures account_inv();
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate bank_inv() =
            this.store |-> ?s
        &*& this.nelems |-> ?n
        &*& this.capacity |-> ?cap
        &*& s != null
        &*& s.length == cap
        &*& 0 < n
        &*& n <= cap
        &*& s[n - 1] |-> ?last
        &*& last != null;
    @*/

    public Account retrieveLastAccount()
    //@ requires bank_inv();
    //@ ensures this.store |-> ?s &*& this.nelems |-> ?n2 &*& this.capacity |-> ?cap2 &*& s != null &*& s.length == cap2 &*& 0 <= n2 &*& n2 < cap2 &*& s[n2] |-> result &*& result != null;
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}