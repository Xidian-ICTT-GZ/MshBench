class Account {
    int balance;

    public Account() {
        balance = 0;
    }
}

public class Bank {
    Account[] store;
    int nelems;
    int capacity;

    //@ requires this.store != null &*& this.nelems >= 0 &*& this.capacity == store.length &*& this.nelems > 0 &*& (forall int i; 0 <= i < this.nelems ==> this.store[i] != null);
    //@ ensures this.store != null &*& this.nelems == old(this.nelems) - 1 &*& this.capacity == old(this.capacity) &*& result == old(store[old(nelems) - 1]) &*& store[old(nelems) - 1] == null &*& (forall int i; 0 <= i < old(nelems) - 1 ==> store[i] == old(store[i])) &*& (forall int i; old(nelems) - 1 < i < old(capacity) ==> store[i] == old(store[i]));
    public Account retrieveLastAccount() {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}