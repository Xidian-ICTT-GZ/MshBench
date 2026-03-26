/*@ predicate account(Account a; int b) = a->balance |-> b; @*/

/*@ predicate bank(Bank b; Account[] s, int n, int cap) =
    b->store |-> s &*& b->nelems |-> n &*& b->capacity |-> cap &*&
    0 <= n &*& n <= cap &*&
    array_slice(s, 0, n, ?elems) &*&
    foreach(elems, (account)(Account.class)) &*&
    array_slice(s, n, cap, ?nulls) &*&
    foreach(nulls, (is_null)()); @*/

class Account {
    int balance;

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

    //@ requires bank(this, ?s, ?n, ?cap) &*& n > 0;
    //@ ensures bank(this, s, n - 1, cap) &*& account(result, _);
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}