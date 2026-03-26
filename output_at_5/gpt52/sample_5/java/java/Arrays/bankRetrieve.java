class Account {
    int balance;

    /*@
    predicate AccountInv() = this.balance |-> ?b;
    @*/

    public Account()
    //@ requires true;
    //@ ensures AccountInv();
    
    
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
        this.store |-> ?s &*&
        this.nelems |-> ?n &*&
        this.capacity |-> ?c &*&
        s != null &*&
        0 <= n &*& n <= c &*&
        s.length == c &*&
        array_slice(s, 0, c, ?elems);
    @*/

    public Account retrieveLastAccount()
    //@ requires BankInv() &*& 0 < ?n;
    //@ ensures BankInv();
    
    
    {
        //@ open BankInv();
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close BankInv();
        return c;
    }
}