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
    predicate_ctor Account_pred(Account a) = a.balance |-> _;
    predicate_ctor Bank_pred(Bank b; int cap) =
        b.store |-> ?s &*& b.nelems |-> ?n &*& b.capacity |-> cap &*&
        0 <= n &*& n <= cap &*&
        array_slice(s, 0, n, Account_pred);
    @*/

    //@ requires cap >= 0;
    //@ ensures Bank_pred(this, cap);
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close Bank_pred(this, cap);
    }

    //@ requires Bank_pred(this, ?cap);
    //@ ensures Bank_pred(this, cap);
    public void addNewAccount()
    {
        //@ open Bank_pred(this, cap);
        Account c = new Account();
        //@ close Account_pred(c);
        store[nelems] = c;
        nelems = nelems + 1;
        //@ close Bank_pred(this, cap);
    }
}