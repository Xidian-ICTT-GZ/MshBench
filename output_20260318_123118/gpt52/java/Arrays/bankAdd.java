class Account {
    int balance;

    /*@ predicate AccountInv() = this.balance |-> ?b; @*/

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

    /*@ predicate BankInv(int cap, int n) =
            this.capacity |-> cap
        &*& this.nelems |-> n
        &*& this.store |-> ?arr
        &*& arr != null
        &*& arr.length == cap
        &*& 0 <= n
        &*& n <= cap
        &*& array_slice(arr, 0, cap, ?vs);
    @*/

    public Bank(int cap)
    //@ requires 0 <= cap;
    //@ ensures BankInv(cap, 0);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires BankInv(?cap, ?n) &*& n < cap;
    //@ ensures BankInv(cap, n + 1);
    {
        Account c = new Account();
        store[nelems] = c;

        nelems = nelems + 1;
    }
}