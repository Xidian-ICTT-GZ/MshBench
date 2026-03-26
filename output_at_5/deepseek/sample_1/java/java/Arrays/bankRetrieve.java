class Account {
    int balance;

    //@ predicate AccountPred() = balance |-> _;
    
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

    //@ predicate BankPred() = store |-> ?s &*& nelems |-> ?n &*& capacity |-> ?c &*& s != null &*& 0 <= n &*& n <= c &*& c == s.length &*& array_slice(s, 0, n, Account.AccountPred) &*& array_slice(s, n, c, _);

    public Account retrieveLastAccount()
    //@ requires BankPred() &*& nelems > 0;
    //@ ensures BankPred() &*& result != null &*& Account.AccountPred(result);
    {
        //@ open BankPred();
        Account c = store[nelems - 1];
        //@ array_slice_split(store, nelems-1, nelems);
        //@ array_slice_split(store, 0, nelems-1);
        //@ close array_slice(store, nelems-1, nelems, Account.AccountPred);
        //@ open array_slice(store, nelems-1, nelems, Account.AccountPred);
        //@ open Account.AccountPred(c);
        store[nelems - 1] = null;
        //@ close array_slice(store, nelems-1, nelems, _);
        nelems = nelems - 1;
        //@ array_slice_merge(store, 0, nelems);
        //@ array_slice_merge(store, nelems, capacity);
        //@ close BankPred();
        //@ close Account.AccountPred(c);
        return c;
    }
}