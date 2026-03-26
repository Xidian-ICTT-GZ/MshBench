/*@ predicate account(Account a; int bal) = a.balance |-> bal; @*/

/*@ predicate bank(Bank b; Account[] accounts, int nelems, int capacity) =
    b.store |-> accounts &*&
    b.nelems |-> nelems &*&
    b.capacity |-> capacity &*&
    0 <= nelems &*& nelems <= capacity &*&
    array_slice(accounts, 0, nelems, ?elems) &*&
    foreach(elems, (account)(Account a) -> true) &*&
    array_slice(accounts, nelems, capacity, ?rest) &*&
    foreach(rest, (account)(Account a) -> a == null);
@*/

class Account {
    int balance;

    //@ requires true;
    //@ ensures account(this, 0);
    public Account()
    {
        balance = 0;
        //@ close account(this, 0);
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ requires bank(this, ?accounts, ?nelems0, ?cap) &*& nelems0 > 0;
    //@ ensures bank(this, ?newAccounts, nelems0 - 1, cap) &*& result == accounts[nelems0 - 1];
    public Account retrieveLastAccount()
    {
        //@ open bank(this, _, _, _);
        //@ assert array_slice(store, 0, nelems, ?elems);
        //@ assert array_slice(store, nelems, capacity, ?rest);
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close bank(this, store, nelems, capacity);
        return c;
    }
}