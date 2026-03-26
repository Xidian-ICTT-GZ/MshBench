class Account {
    int balance;

    //@ ensures this.balance |-> 0;
    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ predicate valid() = this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& 0 <= n &*& n <= c &*& s != null;

    //@ requires cap > 0;
    //@ ensures valid() &*& this.capacity |-> cap &*& this.nelems |-> 0;
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires valid() &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& n < c;
    //@ ensures valid() &*& this.nelems |-> (n + 1);
    public void addNewAccount()
    {
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
    }
}