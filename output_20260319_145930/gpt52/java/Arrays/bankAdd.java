class Account {
    int balance;

    /*@
    predicate AccountInv() = this.balance |-> ?b;
    @*/

    public Account()
    //@ requires this.balance |-> _;
    //@ ensures AccountInv() &*& this.balance |-> 0;
    {
        balance = 0;
    }
}

public class Bank {

    Account[] store;
    int nelems;
    int capacity;

    /*@
    predicate BankInv() =
        this.store |-> ?s &*& this.nelems |-> ?n &*& this.capacity |-> ?cap &*&
        s != null &*& n >= 0 &*& n <= cap &*&
        s.length == cap &*&
        array_slice(s, 0, cap, ?elems) &*&
        take(n, elems) == ?prefix &*& foreach(prefix, AccountInv) &*&
        drop(n, elems) == ?suffix &*& foreach(suffix, (nop)(_));
    @*/

    public Bank(int cap)
    //@ requires cap >= 0 &*& this.store |-> _ &*& this.nelems |-> _ &*& this.capacity |-> _;
    //@ ensures BankInv();
    {
        capacity = cap;
        store = new Account[cap];
        nelems = 0;
        //@ close foreach(nil, AccountInv);
        //@ close foreach(_, (nop)(_)); // for suffix; will be rewritten below
        //@ open BankInv();
        //@ close BankInv();
    }

    public void addNewAccount()
    //@ requires BankInv();
    //@ ensures BankInv();
    {
        //@ open BankInv();
        Account c = new Account();
        //@ open c.AccountInv();
        //@ close c.AccountInv();
        store[nelems] = c;
        //@ array_slice_update(store, nelems, c);
        //@ assert array_slice(store, 0, capacity, ?elems2);
        //@ assert take(nelems, elems2) == ?prefix;
        //@ assert drop(nelems, elems2) == ?suffix;
        //@ open foreach(suffix, (nop)(_));
        //@ close foreach(suffix, (nop)(_));
        nelems = nelems + 1;
        //@ close foreach(cons(c, nil), AccountInv);
        //@ close foreach(prefix, AccountInv);
        //@ close BankInv();
    }
}