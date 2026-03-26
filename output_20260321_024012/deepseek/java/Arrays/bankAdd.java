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

    //@ predicate BankPred() = store |-> ?s &*& s != null &*& s.length == capacity &*& capacity |-> _ &*& nelems |-> ?n &*& 0 <= n &*& n <= capacity &*& array_slice(s, 0, n, Account.AccountPred) &*& array_slice(s, n, capacity, any);

    public Bank(int cap)
    //@ requires cap >= 0;
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
        Account c = new Account();
        //@ close Account.AccountPred();
        store[nelems] = c;
        //@ array_slice_split(store, nelems, nelems+1);
        //@ array_slice_close(store, nelems, nelems+1, Account.AccountPred);
        nelems = nelems + 1;
        //@ close BankPred();
    }
}