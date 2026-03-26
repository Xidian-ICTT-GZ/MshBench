class Account {
    int balance;

    /*@ predicate account(Account a; int balance) =
        a.balance |-> balance;
    @*/

    //@ requires true;
    //@ ensures account(this, 0);
    public Account() {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate bank(Bank b; Account[] store, int nelems, int capacity) =
        b.store |-> store &*&
        b.nelems |-> nelems &*&
        b.capacity |-> capacity &*&
        0 <= nelems &*& nelems <= capacity &*&
        capacity <= store.length &*&
        array_slice(store, 0, nelems, ?elems) &*&
        foreach(elems, account);
    @*/

    //@ requires bank(this, ?store, ?nelems, ?capacity) &*& nelems > 0;
    //@ ensures bank(this, store, nelems - 1, capacity) &*& account(result, _);
    public Account retrieveLastAccount() {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}