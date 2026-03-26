class Account {
    int balance;

    public Account()
    //@ requires true;
    //@ ensures this.balance |-> 0;
    {
        balance = 0;
    }
}

/*@ predicate account(Account a;) =
    a != null &*& a.balance |-> ?b;
@*/

/*@ predicate_ctor account_at(Account[] arr, int i)() =
    arr[i] |-> ?a &*& a != null &*& account(a);
@*/

/*@ predicate_ctor null_at(Account[] arr, int i)() =
    arr[i] |-> null;
@*/

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures this.capacity |-> cap &*& this.nelems |-> 0 &*& this.store |-> ?arr &*& arr != null &*& array_slice<Account>(arr, 0, cap, ?elems) &*& all_eq(elems, null) == true;
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires this.capacity |-> ?cap &*& cap > 0 &*& this.store |-> ?arr &*& arr != null &*& this.nelems |-> ?n &*& 0 <= n &*& n < cap &*& array_slice<Account>(arr, 0, cap, ?elems) &*& length(elems) == cap;
    //@ ensures this.capacity |-> cap &*& this.store |-> arr &*& this.nelems |-> n + 1 &*& array_slice<Account>(arr, 0, cap, ?elems2) &*& length(elems2) == cap;
    {
        Account c = new Account();
        //@ close account(c);
        store[nelems] = c;
        nelems = nelems + 1;
    }
}