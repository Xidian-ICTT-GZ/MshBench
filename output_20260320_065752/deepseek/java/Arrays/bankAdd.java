class Account {
    int balance;

    //@ predicate AccountPred() = balance |-> 0;

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
        &*& c == s.length
        &*& 0 <= n &*& n <= c
        &*& array_slice(s, 0, n, Account.AccountPred)
        &*& array_slice(s, n, c, any);
    @*/

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures BankPred();
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close BankPred();
    }

    public void addNewAccount()
    //@ requires BankPred();
    //@ ensures BankPred();
    {
        //@ open BankPred();
        //@ assert nelems |-> ?n &*& capacity |-> ?c &*& store |-> ?s;
        //@ assert 0 <= n &*& n < c;
        Account c = new Account();
        //@ close Account.AccountPred();
        store[nelems] = c;
        //@ array_slice_split(store, n, n+1);
        //@ array_slice_close(store, n, n+1, Account.AccountPred);
        nelems = nelems + 1;
        //@ close BankPred();
    }
}