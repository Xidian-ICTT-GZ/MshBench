class Account {
    int balance;

    public Account()
    
    
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    

    /*@
    predicate validBank(Bank b) = 
        b != null &*&
        0 <= b.nelems &*& b.nelems <= b.capacity &*&
        (b.store == null ? true : (b.store.length == b.capacity &*&
            forAll(int i; 0 <= i && i < b.nelems; b.store[i] != null)));
    @*/

    //@ requires validBank(this);
    //@ ensures validBank(result);
    public Account retrieveLastAccount()
    
    
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}