class Account {
    int balance;

    //@ predicate Account() = balance |-> 0;

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

    /*@
    predicate Bank(int n, int c) =
        store |-> ?a
        &*& a != null
        &*& nelems |-> n
        &*& capacity |-> c
        &*& c == a.length
        &*& 0 <= n &*& n <= c
        &*& array_slice(a, 0, n, Account, _)
        &*& array_slice(a, n, c, Account, ?rest)
        &*& all_eq(rest, null);
    @*/

    //@ predicate all_eq(list<Object> l, Object v) = l == nil ? true : l.head == v &*& all_eq(l.tail, v);

    public Account retrieveLastAccount()
    //@ requires Bank(?n, ?c) &*& n > 0;
    //@ ensures Bank(n-1, c) &*& result.Account();
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}