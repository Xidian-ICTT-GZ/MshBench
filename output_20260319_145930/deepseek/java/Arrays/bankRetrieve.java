class Account {
    int balance;

    //@ predicate Account() = balance |-> 0;

    public Account()
    //@ requires true;
    //@ ensures Account();
    {
        balance = 0;
        //@ close Account();
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ predicate Bank(int c, int n) = store |-> ?s &*& s != null &*& s.length == c &*& capacity |-> c &*& nelems |-> n &*& 0 <= n &*& n <= c &*& array_slice(s, 0, n, Account.Account) &*& array_slice(s, n, c, _);

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures Bank(cap, 0);
    {
        store = new Account[cap];
        capacity = cap;
        nelems = 0;
        //@ close Bank(cap, 0);
    }

    public Account retrieveLastAccount()
    //@ requires Bank(?c, ?n) &*& n >= 1;
    //@ ensures Bank(c, n-1) &*& result.Account();
    {
        //@ open Bank(c, n);
        Account c = store[nelems - 1];
        //@ array_slice_split(nelems-1, nelems);
        //@ open Account.Account() at (store[nelems - 1]);
        store[nelems - 1] = null;
        //@ array_slice_merge(nelems-1);
        nelems = nelems - 1;
        //@ close Bank(c, nelems);
        return c;
    }
}