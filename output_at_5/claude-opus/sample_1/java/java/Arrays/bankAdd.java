class Account {
    int balance;

    /*@ predicate account_p(Account acc; int bal) = acc.balance |-> bal; @*/

    public Account()
    //@ requires true;
    //@ ensures account_p(this, 0);
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate bank_p(Bank b; Account[] st, int n, int cap) =
          b.store |-> st &*&
          b.nelems |-> n &*&
          b.capacity |-> cap &*&
          st != null &*&
          0 <= n &*& n <= cap &*&
          array(store, cap, ?arr) &*&
          length(store) == cap &*& 
          array(store, cap, arr);
    @*/

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures bank_p(this, store, nelems, capacity);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires bank_p(this, store, nelems, capacity) &*& nelems < capacity;
    //@ ensures bank_p(this, store, nelems + 1, capacity);
    {
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
    }
}