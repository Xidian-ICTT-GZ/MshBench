class Account {
    int balance;

    //@ predicate Account() = this.balance |-> 0;

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

    //@ predicate Bank(int cap) = this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> cap &*& s != null &*& s.length == cap &*& array_slice(s, 0, n, Account.Account) &*& array_slice(s, n, cap, any);

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures Bank(cap);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close array_slice(store, 0, 0, any);
        //@ close array_slice(store, 0, cap, any);
        //@ close Bank(cap);
    }

    public void addNewAccount()
    //@ requires Bank(?cap) &*& nelems < cap;
    //@ ensures Bank(cap);
    {
        Account c = new Account();
        //@ open Bank(cap);
        store[nelems] = c;
        //@ open array_slice(store, nelems, capacity, any);
        //@ close array_slice(store, nelems, nelems + 1, Account.Account);
        //@ close array_slice(store, nelems + 1, capacity, any);
        //@ array_slice_join(store);
        nelems = nelems + 1;
        //@ close Bank(cap);
    }
}