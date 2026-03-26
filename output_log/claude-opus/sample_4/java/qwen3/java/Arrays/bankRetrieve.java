class Account {
    int balance;

    public Account()
    //@ requires true;
    //@ ensures balance == 0;
    {
        balance = 0;
    }
}

/*@ predicate account_inv(Account a) =
    a != null &*& a.balance |-> ?b;
@*/

/*@ predicate array_pred(Account[] arr, int length, (Account -> predicate) P) =
    length == 0 ?
        emp
    :
        arr |-> ?a &*& length > 0 &*& 0 <= ?i &*& i < length &*&
        P(arr[i]) &*&
        array_pred(arr, length - 1, P);
@*/

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ invariant 0 <= nelems &*& nelems <= capacity &*&
    //@           store |-> ?arr &*&
    //@           array_pred(arr, capacity, account_inv) &*&
    //@           true; // no extra invariant here

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures capacity == cap &*& nelems == 0 &*&
    //@         store |-> ?arr &*&
    //@         array_pred(arr, cap, account_inv);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public Account retrieveLastAccount()
    //@ requires 0 < nelems &*&
    //@          store |-> ?arr &*&
    //@          array_pred(arr, capacity, account_inv);
    //@ ensures  result != null &*&
    //@          store |-> arr &*&
    //@          array_pred(arr, capacity, account_inv) &*&
    //@          nelems == old(nelems) - 1 &*&
    //@          arr[old(nelems)-1] == null &*&
    //@          result == old(arr)[old(nelems)-1];
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}