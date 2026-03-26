class Account {
    int balance;
    /*@
    predicate account(this) = this->balance |-> _;
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
    predicate bank(this) = 
        this->store |-> ?storePtr &*&
        this->nelems |-> ?n &*& 0 <= n &*& n <= this.capacity &*&
        this->capacity |-> ?cap &*&
        array(storePtr, cap, ?accounts) &*&
        (forall<int>(0, n, (i -> accounts[i] != null && account(accounts[i])))) &*&
        (forall<int>(n, cap, (i -> accounts[i] == null)));
    @*/

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures bank(this);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires bank(this) &*& nelems < capacity;
    //@ ensures bank(this) &*& nelems == old(nelems) + 1;
    {
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
    }
}