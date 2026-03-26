class Account {
    int balance;
    /*@
    predicate accountInv(Account this) = this.balance |-> _;
    @*/

    public Account()
        //@ requires true;
        //@ ensures accountInv(this);
    {
        balance = 0;
        //@ close accountInv(this);
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;
    /*@
    predicate bankInv(Bank this) = 
        this.store |-> ?s &*&
        this.nelems |-> ?n &*&
        this.capacity |-> ?c &*&
        s != null &*& 0 <= n &*& n <= c &*&
        array_slice(s, 0, n, ?as) &*&
        length(s) == c &*&
        array_contents(s, as) &*&
        foreach(as, (Account a) -> accountInv(a));
    @*/

    public Bank(int cap)
        //@ requires cap >= 0;
        //@ ensures bankInv(this);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close bankInv(this);
    }

    public void addNewAccount()
        //@ requires bankInv(this);
        //@ ensures bankInv(this);
    {
        //@ open bankInv(this);
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
        //@ close bankInv(this);
    }
}