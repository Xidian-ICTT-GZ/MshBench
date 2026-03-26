class Account {
    int balance;

    //@ ensures true;
    public Account() {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate valid() =
        this.store != null &*&
        this.nelems >= 0 &*&
        this.capacity == this.store.length &*&
        this.nelems <= this.capacity &*&
        (forall int i; 0 <= i &*& i < this.nelems ==> this.store[i] != null) &*&
        (forall int i; this.nelems <= i &*& i < this.capacity ==> this.store[i] == null);
    @*/

    //@ requires valid() &*& this.nelems > 0;
    //@ ensures valid() &*& result == old(this.store[old(this.nelems) - 1]) &*& this.nelems == old(this.nelems) - 1;
    public Account retrieveLastAccount() {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}