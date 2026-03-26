class Account {
    int balance;

    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate valid() =
        store != null &*&
        0 <= nelems &*& nelems <= capacity &*&
        capacity <= store.length &*&
        foreach(store, 0, nelems, account_pred) &*&
        foreach(store, nelems, store.length, (Account)null);
    @*/

    /*@
    predicate account_pred(Account a) =
        a != null &*& a |-> ?balance &*& balance >= 0;
    @*/

    //@ requires valid() &*& nelems > 0;
    //@ ensures valid() &*& result != null &*& account_pred(result);
    public Account retrieveLastAccount()
    {
        //@ open valid();
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close valid();
        return c;
    }
}