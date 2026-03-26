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

    /*@
    predicate BankPred() = 
        store |-> ?s
        &*& nelems |-> ?n
        &*& capacity |-> ?c
        &*& s != null
        &*& 0 <= n &*& n <= c
        &*& c == s.length
        &*& array_slice(s, 0, n, Account.AccountPred)
        &*& array_slice(s, n, c, _);
    @*/

    public Account retrieveLastAccount()
    //@ requires BankPred() &*& nelems > 0;
    //@ ensures BankPred() &*& result.AccountPred();
    {
        //@ open BankPred();
        Account c = store[nelems - 1];
        //@ array_slice_split(nelems - 1, nelems);
        //@ open Account.AccountPred();
        store[nelems - 1] = null;
        //@ array_slice_merge(nelems - 1);
        nelems = nelems - 1;
        //@ close BankPred();
        return c;
    }
}