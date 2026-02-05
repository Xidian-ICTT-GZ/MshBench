/*@
predicate AccountInv(Account a; int bal) =
    a.balance |-> bal;
@*/
class Account {
    int balance;

    public Account()
    //@ requires true;
    //@ ensures AccountInv(this, 0);
    {
        balance = 0;
    }
}

/*@
predicate AccountP(unit u, Account a; unit v) =
    AccountInv(a, ?b) &*& v == unit;
@*/

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankInv(int n, int m) =
        this.store |-> ?arr
    &*& this.nelems |-> n
    &*& this.capacity |-> m
    &*& m > 0
    &*& arr.length == m
    &*& 0 <= n &*& n <= m
    &*& array_slice_deep(arr, 0, n, AccountP, unit, _, _)
    &*& array_slice(arr, n, m, ?rest)
    &*& all_eq(rest, null) == true;
    @*/

    public Bank(int cap)
    //@ requires cap > 0;
    //@ ensures BankInv(0, cap);
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
    }

    public void addNewAccount()
    //@ requires BankInv(?n, ?m) &*& n < m;
    //@ ensures BankInv(n + 1, m);
    {
        Account c = new Account();
        store[nelems] = c;
        //@ array_slice_deep_close(store, n, AccountP, unit);
        nelems = nelems + 1;
    }
}
