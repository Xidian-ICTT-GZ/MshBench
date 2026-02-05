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

    public Account retrieveLastAccount()
    //@ requires BankInv(?n, ?m) &*& n > 0;
    //@ ensures BankInv(n - 1, m) &*& AccountInv(result, _);
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}
