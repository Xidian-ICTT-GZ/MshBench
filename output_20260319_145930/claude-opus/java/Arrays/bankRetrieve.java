/*@
predicate Account(Account a;) =
    a.balance |-> _;
@*/

class Account {
    int balance;

    public Account()
    //@ requires true;
    //@ ensures Account(this);
    {
        balance = 0;
        //@ close Account(this);
    }
}

/*@
predicate_ctor Account_at(int i)(Account a) =
    a == null ? true : Account(a);

predicate Bank_store(Account[] arr, int len;) =
    arr != null &*& array_slice_deep(arr, 0, len, Account_at, unit, _, _);

predicate Bank(Bank b;) =
    b.store |-> ?arr &*&
    b.nelems |-> ?n &*&
    b.capacity |-> ?cap &*&
    arr != null &*&
    arr.length == cap &*&
    0 <= n &*& n <= cap &*&
    Bank_store(arr, cap);
@*/

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    public Account retrieveLastAccount()
    //@ requires Bank(this) &*& this.nelems |-> ?n &*& n > 0;
    //@ ensures Bank(this) &*& Account(result);
    {
        //@ open Bank(this);
        //@ open Bank_store(store, capacity);
        Account c = store[nelems - 1];
        //@ open Account_at(nelems - 1)(c);
        store[nelems - 1] = null;
        //@ close Account_at(nelems - 1)(null);
        //@ close Bank_store(store, capacity);
        nelems = nelems - 1;
        //@ close Bank(this);
        return c;
    }
}