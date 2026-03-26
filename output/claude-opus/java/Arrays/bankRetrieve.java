class Account {
    int balance;

    //@ predicate Account(int b) = balance |-> b;

    //@ requires true;
    //@ ensures Account(0);
    public Account()

    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate Bank(int n, int cap) = 
        store |-> ?arr &*& 
        nelems |-> n &*& 
        capacity |-> cap &*&
        arr != null &*&
        array_slice(arr, 0, n, ?elems) &*&
        array_slice(arr, n, cap, _) &*&
        0 <= n &*& n <= cap &*& cap == arr.length;
    @*/

    //@ requires Bank(?n, ?cap) &*& n > 0;
    //@ ensures Bank(n - 1, cap) &*& result != null &*& result.Account(?b);
    public Account retrieveLastAccount()

    {
        //@ open Bank(n, cap);
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close Bank(nelems, cap);
        return c;
    }
}