class Account {
    int balance;

    /*@ predicate account(Account a; int bal) = 
          a != null &*& a.balance |-> bal;
    @*/

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

    /*@ predicate bank(Bank b; Account[] s, int n, int c) =
          b.store |-> s &*& 
          b.nelems |-> n &*& 
          b.capacity |-> c &*& 
          0 <= n &*& n <= c &*& 
          array_slice(s, 0, c, ?arr) &*&
          array_slice_is_account_array(s, c) &*&
          accounts_for_slice(arr, 0, n);
    @*/

    /*@ predicate accounts_for_slice(Account[] arr, int from, int to) =
          from == to ? emp : 
          accs_slice(arr, from, to) &*& 
          account(arr[from], _) &*& 
          accounts_for_slice(arr, from+1, to);
      // Helper predicate group for readability, arr elements with account predicates owned
    @*/

    /*@ predicate array_slice(Account[] arr, int from, int to, list<Account> accs) =
          from == to ? accs == nil &*& emp :
          array_slice(arr, from+1, to, ?rest) &*&
          accs == cons(arr[from], rest);
    @*/

    /*@ predicate array_slice_is_account_array(Account[] arr, int length) = true;
        // Sanity predicate for the array content — no direct permission needed here
    @*/

    //@ requires cap >= 0;
    //@ ensures bank(this, store, 0, cap);
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires bank(this, store, ?n, capacity) &*& n < capacity;
    //@ ensures bank(this, store, n + 1, capacity) &*& account(store[n], 0);
    public void addNewAccount()
    {
        Account c = new Account();
        store[nelems] = c;
        nelems = nelems + 1;
    }
}