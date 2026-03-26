class Account {
    int balance;

    /*@
    predicate account(this) = this.balance |-> _;
    @*/

    public Account()
    //@ requires true;
    //@ ensures account(this);
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate bank(this) = this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& array_slice(s, 0, n, ?accounts);
    @*/

    //@ predicate array_slice(Account[] arr, int from, int to, list<Account> accounts) = true;
    //@ fixpoint list<Account> take(int n, list<Account> l) {
    //@     switch(l) {
    //@         case nil: return nil;
    //@         case cons(h, t): return n == 0 ? nil : cons(h, take(n-1, t));
    //@     }
    //@ }

    public Account retrieveLastAccount()
    //@ requires bank(this) &*& 0 < nelems &*& nelems <= capacity &*& store != null;
    //@ ensures bank(this) &*& result != null;
    {
        //@ open bank(this);
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close bank(this);
        return c;
    }
}