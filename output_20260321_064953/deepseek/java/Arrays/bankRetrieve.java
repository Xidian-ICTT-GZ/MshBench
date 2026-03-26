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

    //@ predicate Bank() = store |-> ?s &*& nelems |-> ?n &*& capacity |-> ?c &*& s != null &*& 0 <= n &*& n <= c &*& c == s.length &*& array_slice(s, 0, n, Account.Account) &*& array_slice(s, n, c, _);

    public Account retrieveLastAccount()
    //@ requires Bank();
    //@ ensures Bank() &*& result != null ? Account.Account(result) : true;
    {
        //@ open Bank();
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close Bank();
        return c;
    }
}