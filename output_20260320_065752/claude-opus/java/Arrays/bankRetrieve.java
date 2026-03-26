class Account {
    int balance;
    /*@
    predicate inv() = this.balance |-> balance;
    @*/

    public Account()
    //@ requires true;
    //@ ensures inv();
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;
    /*@
    predicate inv() =
        this.store |-> store &*&
        this.nelems |-> nelems &*&
        this.capacity |-> capacity &*&
        0 <= nelems &*& nelems <= capacity &*&
        array_slice(store, 0, capacity, ?a) &*&
        array_slice(store, 0, nelems, ?used) &*&
        all_non_null_or_null(used);

    fixpoint<bool> all_non_null_or_null(list<Account> l) {
      switch(l) {
        case nil: return true;
        case cons(h, t): return (h != null) && all_non_null_or_null(t);
      }
    }
    @*/

    public Account retrieveLastAccount()
    //@ requires inv() &*& nelems > 0;
    //@ ensures inv() &*& result == store[nelems];
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}