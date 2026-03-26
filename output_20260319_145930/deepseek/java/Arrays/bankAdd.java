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

    /*@
    predicate Bank(int cap) = 
        store |-> ?s
        &*& nelems |-> ?n
        &*& capacity |-> cap
        &*& s != null
        &*& s.length == cap
        &*& 0 <= n &*& n <= cap
        &*& array_slice(s, 0, n, Account.Account)
        &*& array_slice(s, n, cap, _);
    @*/

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures Bank(cap);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close Bank(cap);
    }

    public void addNewAccount()
    //@ requires Bank(?cap) &*& nelems < capacity;
    //@ ensures Bank(cap);
    {
        Account c = new Account();
        //@ open Bank(cap);
        store[nelems] = c;
        //@ array_slice_split(store, nelems, nelems+1);
        //@ close array_slice(store, nelems, nelems+1, Account.Account);
        //@ array_slice_merge(store, nelems, nelems+1, capacity);
        nelems = nelems + 1;
        //@ close Bank(cap);
    }
}