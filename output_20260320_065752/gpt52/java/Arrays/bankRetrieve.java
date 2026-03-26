class Account {
    int balance;

    /*@
    predicate Account_inv(Account a) = a.balance |-> ?b;
    @*/

    public Account()
    //@ requires this.balance |-> _;
    //@ ensures Account_inv(this);
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate Bank_inv(Bank b) =
        b.store |-> ?s &*& b.nelems |-> ?n &*& b.capacity |-> ?cap &*& s != null &*& s.length == cap &*& 0 < n &*& n <= cap;
    @*/

    public Account retrieveLastAccount()
    //@ requires Bank_inv(this) &*& this.store != null &*& this.nelems > 0;
    //@ ensures Bank_inv(this);
    {
        //@ open Bank_inv(this);
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close Bank_inv(this);
        return c;
    }
}