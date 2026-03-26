/*@ predicate account(Account a; int b) = a->balance |-> b; @*/

/*@ predicate bank(Bank b; Account[] store, int nelems, int capacity) =
    b->store |-> ?s &*& b->nelems |-> nelems &*& b->capacity |-> capacity &*&
    0 <= nelems &*& nelems <= capacity &*&
    array_slice(s, 0, nelems, ?accounts) &*&
    foreach(accounts, account_pred) &*&
    array_slice(s, nelems, capacity, _) &*&
    malloc_block_array(s, capacity);
@*/

/*@ predicate account_pred(Account a) = account(a, _); @*/

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

    //@ requires bank(this, ?store0, ?nelems0, ?capacity0) &*& nelems0 > 0;
    //@ ensures bank(this, store0, nelems0 - 1, capacity0) &*& account(result, _);
    public Account retrieveLastAccount()
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}