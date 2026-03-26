class Account {
    int balance;

    /*@
    predicate account(int b) = balance |-> b;
    @*/

    public Account()
    //@ requires true;
    //@ ensures account(0);
    {
        balance = 0;
        //@ close account(0);
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate bank(Account[] s, int n, int c) =
        store |-> s &*& nelems |-> n &*& capacity |-> c &*&
        0 <= n &*& n <= c &*&
        array_slice(s, 0, n, ?elems) &*&
        foreach(elems, (Account a) => a != null ? account(?b) : true);
    @*/

    public Account retrieveLastAccount()
    //@ requires bank(?s, ?n, ?c) &*& n > 0;
    //@ ensures bank(s, n - 1, c) &*& result != null &*& account(?b);
    {
        //@ open bank(s, n, c);
        //@ assert array_slice(s, 0, n, ?elems);
        Account c = store[nelems - 1];
        //@ assert c != null;
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close bank(s, n - 1, c);
        return c;
    }
}