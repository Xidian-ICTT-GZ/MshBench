/*@
predicate Account_balance(Account a; int v) = a.balance |-> v;

predicate Account(Account a;) = a.balance |-> _;

predicate_ctor Account_at(int i)(Account a;) = Account(a);

predicate Bank_store(Bank b; Account[] arr) = b.store |-> arr;
predicate Bank_nelems(Bank b; int n) = b.nelems |-> n;
predicate Bank_capacity(Bank b; int c) = b.capacity |-> c;

predicate Bank(Bank b; Account[] arr, int n, int c) =
    b.store |-> arr &*& b.nelems |-> n &*& b.capacity |-> c &*&
    arr != null &*& arr.length == c &*& 0 <= n &*& n <= c &*&
    array_slice_deep(arr, 0, n, Account_at, unit, _, _) &*&
    array_slice(arr, n, c, _);
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

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    public Bank(int cap)
    //@ requires cap > 0;
    //@ ensures Bank(this, ?arr, 0, cap);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close Bank(this, store, 0, cap);
    }

    public void addNewAccount()
    //@ requires Bank(this, ?arr, ?n, ?c) &*& n < c;
    //@ ensures Bank(this, arr, n + 1, c);
    {
        //@ open Bank(this, arr, n, c);
        Account a = new Account();
        //@ close Account_at(n)(a);
        store[nelems] = a;
        //@ array_slice_deep_close(store, n, Account_at, unit);
        nelems = nelems + 1;
        //@ close Bank(this, store, nelems, c);
    }
}