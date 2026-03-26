class Account {
    int balance;

    //@ predicate Account() = balance |-> 0;

    public Account()
    //@ requires true;
    //@ ensures Account();
    {
        balance = 0;
    }
}

/*@
predicate Bank(Account[] store, int nelems, int capacity) =
    store != null &*&
    store.length == capacity &*&
    0 <= nelems &*& nelems <= capacity &*&
    array_slice(store, 0, nelems, Account, ?elems) &*&
    array_slice(store, nelems, capacity, Account, ?rest) &*&
    all_eq(rest, null) == true;
@*/

/*@
predicate_family all_eq(Object[] arr, Object v)(int i) =
    i >= 0 ?
        (arr[i] == v &*& all_eq(arr, v)(i+1))
    :
        true;
@*/

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    //@ predicate Bank() = Bank(store, nelems, capacity);

    public Account retrieveLastAccount()
    //@ requires Bank() &*& nelems > 0;
    //@ ensures Bank() &*& result.Account();
    {
        Account c = store[nelems - 1];
        store[nelems - 1] = null;
        nelems = nelems - 1;
        return c;
    }
}