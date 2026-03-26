class Account {
int balance;

public Account()
//@ requires true;
//@ ensures balance == 0;
{
    balance = 0;
}

/*@ predicate account(Account a) =
    a != null &*& a.balance |-> ?b;
@*/
}

public class Bank {

Account[] store;
int nelems;
int capacity;

public Bank(int cap)
//@ requires 0 <= cap;
//@ ensures capacity == cap &*& nelems == 0 &*&
//@         store |-> ?arr &*&
//@         arr != null &*&
//@         array_len(arr) == cap &*&
//@         (forall int i; 0 <= i && i < cap ==> arr[i] == null);
{
    capacity = cap;
    store = new Account[cap];
    nelems = 0;
}

public void addNewAccount()
//@ requires capacity > 0 &*&
//@          store |-> ?arr &*&
//@          arr != null &*&
//@          array_len(arr) == capacity &*&
//@          0 <= nelems &*& nelems < capacity &*&
//@          (forall int i; 0 <= i && i < nelems ==> arr[i] != null &*& account(arr[i])) &*&
//@          (forall int i; nelems <= i && i < capacity ==> arr[i] == null);
//@ ensures store |-> ?arr' &*&
//@         arr' != null &*&
//@         array_len(arr') == capacity &*&
//@         0 <= nelems + 1 &*& nelems + 1 <= capacity &*&
//@         (forall int i; 0 <= i && i < nelems + 1 ==> arr'[i] != null &*& account(arr'[i])) &*&
//@         (forall int i; nelems + 1 <= i && i < capacity ==> arr'[i] == null) &*&
//@         nelems == old(nelems) + 1;
{
    Account c = new Account();
    store[nelems] = c;
    nelems = nelems + 1;
}
}