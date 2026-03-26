class Account {
    int balance;

    //@ requires true;
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

    //@ requires this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& n > 0 &*& n <= s.length &*& s[n - 1] != null;
    //@ ensures this.store |-> ?s2 &*& this.nelems |-> (n - 1) &*& this.capacity |-> c &*& result == old_s[n - 1] &*& s2[n - 1] == null &*& forall(i, i >= 0 && i < n - 1 ==> s2[i] == old_s[i]);
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}