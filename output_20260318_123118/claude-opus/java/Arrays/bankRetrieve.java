class Account {
    int balance;

    /*@ predicate account(Account a; int balanceValue) =
          a.balance |-> balanceValue;
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

    /*@ predicate accounts(Bank b; list<Account> accts) =
          b.store |-> ?arr &*& b.nelems |-> ?n &*& b.capacity |-> ?c &*&
          arr.length == c &*& n <= c &*&
          array_segments(arr, 0, n, accts) &*&
          array_contents_null(arr, n, c);
    @*/

    /*@ predicate array_segments(Account[] arr; int start; int end; list<Account> accts) =
          start == end ?
            emp &*& accts == nil
          :
            start < end &*& 
            account(arr[start], ?bal) &*&
            array_segments(arr, start + 1, end, ?tail) &*& accts == cons(arr[start], tail);
    @*/

    /*@ predicate array_contents_null(Account[] arr; int start; int end) =
          start == end ?
            emp
          :
            start < end &*& arr[start] |-> null &*& array_contents_null(arr, start + 1, end);
    @*/

    /*@ requires accounts(this, ?accts) &*& accts != nil; @*/
    /*@ ensures accounts(this, (take(length(accts) - 1, accts))) &*& result == last(accts); @*/
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}