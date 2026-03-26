class Account {
  int balance;

  public Account()
  //@ requires true;
  //@ ensures balance == 0;
  {
    balance = 0;
  }
}

/*@ predicate account(Account a) =
    a != null &*& a.balance |-> ?b;
@*/

public class Bank {

  Account[] store;
  int nelems;
  int capacity;

  //@ predicate bank(Bank b;) =
  //@   b.store |-> ?arr &*& arr != null &*& array_len(arr) == b.capacity &*&
  //@   0 <= b.nelems &*& b.nelems <= b.capacity &*&
  //@   (forall int i; 0 <= i && i < b.nelems ==> arr[i] != null &*& account(arr[i])) &*&
  //@   (forall int i; b.nelems <= i && i < b.capacity ==> arr[i] == null);

  public Bank(int cap)
  //@ requires 0 <= cap;
  //@ ensures capacity == cap &*& nelems == 0 &*& bank(this);
  {
    capacity = cap;
    store = new Account[cap];
    nelems = 0;
  }

  public void addNewAccount()
  //@ requires capacity > 0 &*& bank(this) &*& nelems < capacity;
  //@ ensures bank(this) &*& nelems == old(nelems) + 1;
  {
    Account c = new Account();
    store[nelems] = c;
    nelems = nelems + 1;
  }
}