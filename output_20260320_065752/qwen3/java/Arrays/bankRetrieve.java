/*@ 
predicate account(Account a; int balance) = a.balance |-> balance;
predicate bank(Bank b; Account[] store, int nelems, int capacity) =
    b.store |-> store &*& b.nelems |-> nelems &*& b.capacity |-> capacity;
@*/

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

    //@ requires bank(this, ?store_, ?nelems_, ?capacity_) &*& nelems_ > 0 &*& 0 <= nelems_ - 1 &*& nelems_ - 1 < store_.length;
    //@ ensures bank(this, ?store__, result.nelems, capacity_) &*& account(result, _);
    public Account retrieveLastAccount()
    {
        //@ open bank(this, _, _, _);
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        //@ close bank(this, store, nelems, capacity);
        return c;
    }
}