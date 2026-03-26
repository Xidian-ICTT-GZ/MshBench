class Account {
    int balance;

    //@ predicate Account() = this.balance |-> 0;

    public Account()
    //@ requires true;
    //@ ensures Account();
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ predicate Bank(int n, int c) = store |-> ?s &*& s != null &*& s.length == c &*& capacity |-> c &*& nelems |-> n &*& 0 <= n &*& n <= c &*& array_slice(s, 0, n, Account) &*& array_slice(s, n, c, any);

    public Account retrieveLastAccount()
    //@ requires Bank(?n, ?c) &*& n >= 1;
    //@ ensures Bank(n - 1, c) &*& result.Account();
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}