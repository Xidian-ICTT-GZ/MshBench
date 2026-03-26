/*@ predicate account(Account a; int b) = a.balance |-> b; @*/

/*@ predicate bank(Bank b; Account[] s, int n, int cap) =
    b.store |-> s &*& b.nelems |-> n &*& b.capacity |-> cap &*&
    0 <= n &*& n <= cap &*&
    array_slice(s, 0, n, ?accounts) &*&
    foreach(accounts, account_pred);
@*/

/*@ predicate_family_instance foreach<account_pred>(list<Account> accounts) =
    switch(accounts) {
        case nil: true;
        case cons(h, t): account(h, 0) &*& foreach<account_pred>(t);
    };
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

    //@ requires 0 <= cap;
    //@ ensures bank(this, result, 0, cap) &*& result == store;
    public Bank(int cap)
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    //@ requires bank(this, ?s, ?n, ?cap) &*& n < cap;
    //@ ensures bank(this, s, n + 1, cap);
    public void addNewAccount()
    {
        Account c = new Account();
        store[nelems] = c;
        
        nelems = nelems + 1;
    }
}