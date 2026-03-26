class Account {
    int balance;

    /*@
    predicate Account(int b) =
        this.balance |-> b;
    @*/

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

    /*@
    predicate Bank(int n, int cap) =
        this.capacity |-> cap &*&
        this.nelems |-> n &*&
        this.store |-> ?arr &*&
        arr != null &*&
        array_slice(arr, 0, n, ?elems) &*&
        array_slice(arr, n, cap, _) &*&
        cap >= 0 &*&
        n >= 0 &*&
        n <= cap;
    @*/

    //@ requires cap > 0 &*& cap <= 2147483647;
    //@ ensures Bank(0, cap);
    public Bank(int cap)

    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires Bank(?n, ?cap) &*& n < cap;
    //@ ensures Bank(n + 1, cap);
    public void addNewAccount()

    {
        Account c = new Account();
        store[nelems] = c;

        nelems = nelems + 1;
    }
}