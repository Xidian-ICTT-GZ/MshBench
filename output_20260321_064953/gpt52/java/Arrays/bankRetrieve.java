class Account {
    int balance;

    /*@
    predicate AccountInv() = this.balance |-> ?b;
    @*/

    public Account()
    //@ requires this.balance |-> _;
    //@ ensures this.AccountInv();
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankInv() =
        this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?cap &*&
        s != null &*& s.length == cap &*& 0 < n &*& n <= cap;
    @*/

    public Account retrieveLastAccount()
    //@ requires this.BankInv() &*& this.store != null;
    //@ ensures this.BankInv() &*& result == ?c;
    {
        //@ open this.BankInv();
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close this.BankInv();
        return c;
    }
}