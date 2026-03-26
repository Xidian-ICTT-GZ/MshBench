class Account {
    int balance;

    /*@
    predicate AccountInv(Account a) = a.balance |-> ?b;
    @*/

    public Account()
    //@ requires true;
    //@ ensures AccountInv(this);
    
    
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankInv(Bank b) =
        b.store |-> ?s &*&
        b.nelems |-> ?n &*&
        b.capacity |-> ?c &*&
        s != null &*&
        0 <= n &*& n <= c &*&
        s.length == c &*&
        array_slice(s, 0, c, ?elems);
    @*/

    

    public Account retrieveLastAccount()
    //@ requires BankInv(this) &*& this.nelems > 0;
    //@ ensures BankInv(this);
    
    
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}