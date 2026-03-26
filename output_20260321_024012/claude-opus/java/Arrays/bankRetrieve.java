class Account {
    int balance;
    
    /*@ predicate account(this) = 
          this.balance |-> _;
    @*/

    //@ requires true;
    //@ ensures account(this);
    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate bank(this) = 
          this.store |-> ?store_ &*&
          this.nelems |-> ?nelems_ &*&
          this.capacity |-> ?capacity_;
    @*/

    //@ requires bank(this) &*& nelems > 0 &*& 0 <= nelems && nelems <= capacity;
    //@ ensures bank(this) &*& result != null;
    public Account retrieveLastAccount()
    {
        //@ open bank(this);
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close bank(this);
        return c;
    }
}