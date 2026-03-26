/*@ predicate account(Account a; int bal) = a.balance |-> bal; @*/

/*@ predicate bank(Bank b; Account[] accounts, int nelems, int capacity) =
    b.store |-> accounts &*&
    b.nelems |-> nelems &*&
    b.capacity |-> capacity &*&
    0 <= nelems &*& nelems <= capacity &*&
    array_slice(accounts, 0, nelems, ?elems) &*&
    foreach(elems, account_pred);
@*/

/*@ predicate_family_instance foreach<account_pred>(list<Account> elems); @*/
/*@ predicate account_pred(Account a) = account(a, _); @*/

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

    //@ requires 0 <= cap;
    //@ ensures bank(this, ?accounts, 0, cap) &*& length(accounts) == cap;
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close bank(this, store, 0, cap);
    }

    //@ requires bank(this, ?oldStore, ?oldNelems, ?cap) &*& oldNelems < cap;
    //@ ensures bank(this, ?newStore, oldNelems + 1, cap) &*& length(newStore) == cap;
    public void addNewAccount()
    {
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
        //@ open bank(this, _, _, _);
        //@ close bank(this, store, nelems, capacity);
    }
}