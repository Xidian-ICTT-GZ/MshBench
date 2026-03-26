class Account {
    int balance;

    public Account()
    //@ requires true;
    //@ ensures true;
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate_ctor Bank(Bank b; Account[] store, int nelems, int capacity) =
        b.store |-> ?s &*& b.nelems |-> nelems &*& b.capacity |-> capacity &*&
        s == store &*& 0 <= nelems &*& nelems <= capacity &*&
        array_slice(s, 0, nelems, _);
    @*/

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures Bank(this, result_, nelems_, capacity_) &*& nelems_ == 0 &*& capacity_ == cap;
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close Bank(this, store, nelems, capacity);
    }

    public void addNewAccount()
    //@ requires Bank(this, ?store_, ?nelems_, ?capacity_) &*& nelems_ < capacity_;
    //@ ensures Bank(this, store_, nelems_ + 1, capacity_);
    {
        //@ open Bank(this, store_, nelems_, capacity_);
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
        //@ close Bank(this, store_, nelems, capacity_);
    }
}