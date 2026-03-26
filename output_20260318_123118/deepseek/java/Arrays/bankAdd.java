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
    predicate Bank(int c, int n) =
        store |-> ?a
        &*& a != null
        &*& a.length == c
        &*& capacity |-> c
        &*& nelems |-> n
        &*& 0 <= n &*& n <= c
        &*& array_slice(a, 0, n, Account_Account)
        &*& array_slice(a, n, c, _);
    @*/

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures Bank(cap, 0);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires Bank(?c, ?n) &*& n < c;
    //@ ensures Bank(c, n + 1);
    {
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
    }
}