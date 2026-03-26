class Account {
    int balance;

    /*@ predicate account(Account acc; int bal) = acc.balance |-> bal; @*/

    //@ requires true;
    //@ ensures account(this, 0);
    public Account()
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@ predicate accounts(Bank b; int n) =
          b.store |-> ?arr &*& b.nelems |-> n &*& b.capacity |-> ?cap &*&
          array_slice<Account>(arr, 0, cap, ?accountsList) &*&
          accountsList.length == cap &*&
          0 <= n &*& n <= cap &*&
          (forall<int i; 0 <= i &*& i < n; accountsList[i] != null) &*&
          (forall<int i; n <= i &*& i < cap; accountsList[i] == null);
    @*/

    //@ requires accounts(this, ?n) &*& n > 0;
    //@ ensures accounts(this, n - 1) &*& result == old(store)[n - 1];
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        //@ open accounts(this, nelems);
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close accounts(this, nelems);
        return c;
    }
}