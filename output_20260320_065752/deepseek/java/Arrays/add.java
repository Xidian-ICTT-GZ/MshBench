public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate Bag(int cap) =
        store |-> ?s
        &*& s != null
        &*& s.length == cap
        &*& array_slice(s, 0, cap, _)
        &*& nelems |-> ?n
        &*& 0 <= n &*& n <= cap;
    @*/

    //@ requires 0 <= cap;
    //@ ensures Bag(cap);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
        //@ close Bag(cap);
    }

    //@ requires Bag(?cap);
    //@ ensures Bag(cap) &*& result ? nelems == old(nelems) + 1 : nelems == old(nelems);
    boolean add(int v)
    {
        //@ open Bag(?cap0);
        if(nelems<store.length) {
            //@ assert nelems < store.length;
            store[nelems] = v;
            nelems = nelems+1;
            //@ close Bag(cap0);
            return true;
        } else {
            //@ close Bag(cap0);
            return false;
        }
    }
}