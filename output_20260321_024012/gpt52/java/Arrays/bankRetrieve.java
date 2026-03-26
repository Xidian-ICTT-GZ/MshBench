class Account {
    int balance;

    /*@
    predicate AccountInv() = this.balance |-> ?b;
    @*/

    public Account()
    //@ requires this.balance |-> _;
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
        this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?cap &*&
        s != null &*& 0 <= n &*& n <= s.length &*& cap == s.length &*&
        array_slice(s, 0, s.length, ?elems);
    @*/

    

    public Account retrieveLastAccount()
    //@ requires BankInv() &*& this.nelems |-> ?n0 &*& this.store |-> ?s0 &*& 0 < n0;
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