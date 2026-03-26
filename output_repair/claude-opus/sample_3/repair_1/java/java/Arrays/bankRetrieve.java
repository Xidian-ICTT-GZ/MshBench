/*@
predicate Account_balance(Account a; int v) = a.balance |-> v;
@*/

class Account {
    int balance;

    //@ requires true;
    //@ ensures this.balance |-> 0;
    public Account()
    {
        balance = 0;
    }
}

/*@
predicate Bank_store(Bank b; Account[] s) = b.store |-> s;
predicate Bank_nelems(Bank b; int n) = b.nelems |-> n;
predicate Bank_capacity(Bank b; int c) = b.capacity |-> c;
@*/

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ requires this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?cap &*& s != null &*& n > 0 &*& n <= s.length &*& array_slice(s, 0, s.length, ?elems);
    //@ ensures this.store |-> s &*& this.nelems |-> n - 1 &*& this.capacity |-> cap &*& array_slice(s, 0, s.length, _);
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}