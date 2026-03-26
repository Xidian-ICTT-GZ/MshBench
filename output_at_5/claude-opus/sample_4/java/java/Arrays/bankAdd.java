class Account {
    int balance;

    /*@
    predicate account_p() = this.balance |-> _;
    @*/

    public Account()
    //@ requires true;
    //@ ensures account_p();
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate bank_p() = 
        this.store |-> store &*&
        this.nelems |-> nelems &*&
        this.capacity |-> capacity &*&
        store != null &*&
        0 <= nelems &*& nelems <= capacity &*&
        array(store, capacity, ?accounts);
    @*/

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures bank_p();
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires bank_p() &*& nelems < capacity;
    //@ ensures bank_p() &*& nelems == old(nelems) + 1;
    {
        //@ open bank_p();
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
        //@ close bank_p();
    }
}