class Account {
    int balance;

    //@ predicate AccountPred() = this.balance |-> 0;

    public Account()
    //@ requires true;
    //@ ensures AccountPred();
    {
        balance = 0;
        //@ close AccountPred();
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankPred(int cap, int n) =
        this.store |-> ?s
        &*& this.nelems |-> n
        &*& this.capacity |-> cap
        &*& s != null
        &*& s.length == cap
        &*& 0 <= n &*& n <= cap
        &*& array_slice(s, 0, n, Account.AccountPred)
        &*& array_slice(s, n, cap, _);
    @*/

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures BankPred(cap, 0);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close array_slice(store, 0, cap, _);
        //@ close BankPred(cap, 0);
    }

    public void addNewAccount()
    //@ requires BankPred(capacity, nelems) &*& nelems < capacity;
    //@ ensures BankPred(capacity, nelems + 1);
    {
        Account c = new Account();
        //@ open BankPred(capacity, nelems);
        store[nelems] = c;
        //@ array_slice_store(nelems);
        //@ close Account.AccountPred();
        //@ close array_slice(store, nelems, nelems + 1, Account.AccountPred);
        //@ merge_array_slice(store, nelems);
        nelems = nelems + 1;
        //@ close BankPred(capacity, nelems);
    }
}