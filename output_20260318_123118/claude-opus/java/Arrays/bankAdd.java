class Account {
    int balance;

    /*@ predicate account(Account a; int bal) =
          a.balance |-> bal;
    @*/

    public Account()
    //@ requires true;
    //@ ensures account(this, 0);
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate bank(Bank b; Account[] accs, int n, int cap) =
          b.store |-> accs &*&
          b.nelems |-> n &*&
          b.capacity |-> cap &*&
          0 <= n &*& n <= cap &*&
          accs != null &*&
          accs.length == cap &*&
          array_slice(accs, 0, n, account(?as)) &*&
          // For all stored accounts, we have account predicate
          forall<int i; 0 <= i && i < n; account(accs[i], ?bal));
    @*/

    public Bank(int cap)
    //@ requires cap >= 0;
    //@ ensures bank(this, store, 0, cap);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires bank(this, store, nelems, capacity) &*& nelems < capacity;
    //@ ensures bank(this, store, nelems + 1, capacity);
    {
        Account c = new Account();
        store[nelems] = c;

        nelems = nelems + 1;
    }
}