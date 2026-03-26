class Account {
    int balance;

    /*@
    predicate AccountInv() = this.balance |-> ?b;
    @*/

    //@ requires this.AccountInv();
    //@ ensures this.AccountInv();
    public Account()
    
    
    {
        //@ open this.AccountInv();
        balance = 0;
        //@ close this.AccountInv();
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankInv() =
        this.capacity |-> ?cap &*& this.nelems |-> ?n &*& this.store |-> ?arr &*& arr != null &*& arr.length == cap &*& 0 <= n &*& n <= cap;
    @*/

    //@ requires true;
    //@ ensures this.BankInv();
    public Bank(int cap)
    
    
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close this.BankInv();
    }

    //@ requires this.BankInv();
    //@ ensures this.BankInv();
    public void addNewAccount()
    
    
    {
        //@ open this.BankInv();
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
        //@ close this.BankInv();
    }
}