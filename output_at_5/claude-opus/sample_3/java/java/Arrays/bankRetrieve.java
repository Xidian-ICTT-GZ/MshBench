class Account {
    int balance;
    /*@
    predicate valid() = true;
    @*/

    public Account()
    //@ requires true;
    //@ ensures valid();
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;
    /*@
    predicate valid() = 0 <= nelems && nelems <= capacity &*& store != null;
    @*/

    public Account retrieveLastAccount()
    //@ requires valid() &*& nelems > 0 &*& store[nelems - 1] != null;
    //@ ensures valid() &*& nelems == old(nelems) - 1 &*& result != null;
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ assert nelems == old(nelems) - 1;
        return c;
    }
}