class Account {
    int balance;

    //@ predicate AccountInv() = this.balance |-> _;

    //@ ensures AccountInv();
    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ predicate BankInv() = this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& s != null &*& array_slice(s, 0, s.length, _) &*& 0 <= n &*& n <= c &*& c == s.length;

    //@ requires cap > 0;
    //@ ensures BankInv();
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires BankInv();
    //@ ensures BankInv();
    public void addNewAccount()
        //@ requires this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?c &*& s != null &*& array_slice(s, 0, s.length, _) &*& 0 <= n &*& n < c &*& c == s.length;
        //@ ensures this.store |-> s &*& this.nelems |-> n + 1 &*& this.capacity |-> c &*& array_slice(s, 0, s.length, _);
    {
        Account c = new Account();
        //@ open c.AccountInv();
        store[nelems] = c;
        nelems = nelems + 1;
    }
}