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

    /*@ predicate Bank(Bank b; Account[] s, int n, int c) =
        b.store |-> s &*& b.nelems |-> n &*& b.capacity |-> c &*&
        0 <= n &*& n <= s.length &*&
        forall(i, 0 <= i &*& i < n ==> s[i] != null);
    @*/

    //@ requires Bank(this, ?s, ?n, ?c) &*& n > 0;
    //@ ensures Bank(this, ?s2, n - 1, c) &*& result == s[n - 1] &*& s2[n - 1] == null &*&
    //          forall(i, 0 <= i &*& i < n - 1 ==> s2[i] == s[i]);
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}