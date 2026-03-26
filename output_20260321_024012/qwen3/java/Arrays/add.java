public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate Bag(Bag b; int cap) =
        b.store |-> ?s &*& b.nelems |-> ?n &*&
        s != null &*& array_slice(s, 0, cap, _);
    @*/

    //@ requires cap >= 0;
    //@ ensures Bag(this, cap);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
        //@ close Bag(this, cap);
    }

    //@ requires Bag(this, ?cap);
    //@ ensures Bag(this, cap) &*& result == (nelems < cap);
    boolean add(int v)
    {
        //@ open Bag(this, cap);
        if(nelems < store.length) {
            store[nelems] = v;
            nelems = nelems + 1;
            //@ close Bag(this, cap);
            return true;
        } else {
            //@ close Bag(this, cap);
            return false;
        }
    }
}