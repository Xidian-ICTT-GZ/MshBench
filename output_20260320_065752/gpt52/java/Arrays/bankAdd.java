class Account {
    int balance;

    /*@
    predicate AccountInv() = this.balance |-> ?b;
    @*/

    public Account()
    //@ requires true;
    //@ ensures this.AccountInv();
    {
        balance = 0;
        //@ close AccountInv();
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankInv() =
        this.capacity |-> ?cap &*& cap >= 0 &*&
        this.nelems |-> ?n &*& 0 <= n &*& n <= cap &*&
        this.store |-> ?arr &*& arr != null &*& arr.length == cap &*&
        array_slice(arr, 0, cap, ?vs);
    @*/

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures this.BankInv();
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close BankInv();
    }

    public void addNewAccount()
    //@ requires this.BankInv();
    //@ ensures this.BankInv();
    {
        //@ open BankInv();
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
        //@ close BankInv();
    }
}