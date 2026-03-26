class Account {
    int balance;

    /*@ predicate account(int b) = this.balance |-> b; @*/

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
    predicate bank(Account[] s, int n, int cap) =
        this.store |-> s &*& this.nelems |-> n &*& this.capacity |-> cap &*&
        s != null &*& 0 <= n &*& n <= cap &*& cap == s.length &*&
        array_slice(s, 0, cap, ?vs) &*&
        true;
    @*/

    public Account retrieveLastAccount()
    //@ requires bank(?s, ?n, ?cap) &*& n > 0;
    //@ ensures bank(s, n - 1, cap) &*& result == nth(n - 1, ?vs0);
    {
        //@ open bank(s, n, cap);
        //@ assert array_slice(s, 0, cap, ?vs);
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close bank(s, n - 1, cap);
        return c;
    }
}