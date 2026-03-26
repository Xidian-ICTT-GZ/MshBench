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
        //@ close AccountInv();
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankInv() =
        this.capacity |-> ?cap &*& this.nelems |-> ?n &*& this.store |-> ?arr &*& arr != null &*&
        arr.length == cap &*& 0 <= n &*& n <= cap &*&
        array_slice(arr, 0, cap, ?elems) &*&
        foreach(take(n, elems), Account.account_predicate) &*&
        foreach(drop(n, elems), (Account a) -> a == null);
    @*/

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures BankInv();
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close foreach(nil, Account.account_predicate);
        //@ close foreach(?xs, (Account a) -> a == null);
        //@ close BankInv();
    }

    public void addNewAccount()
    //@ requires BankInv() &*& this.nelems < this.capacity;
    //@ ensures BankInv();
    {
        //@ open BankInv();
        Account c = new Account();
        //@ open Account.AccountInv(c);
        //@ close Account.account_predicate(c);
        //@ assert this.store |-> ?arr;
        //@ assert this.capacity |-> ?cap;
        //@ assert this.nelems |-> ?n;
        //@ assert array_slice(arr, 0, cap, ?elems);
        //@ assert foreach(take(n, elems), Account.account_predicate);
        //@ assert foreach(drop(n, elems), (Account a) -> a == null);
        store[nelems] = c;

        nelems = nelems + 1;
        //@ close BankInv();
    }
}