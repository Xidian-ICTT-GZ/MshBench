public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate Bag(int[] store, int nelems) =
        this.store |-> store &*&
        this.nelems |-> nelems &*&
        store != null &*&
        array_slice(store, 0, store.length, _) &*&
        0 <= nelems &*& nelems <= store.length;
    @*/

    public Bag(int cap)
        //@ requires cap >= 0;
        //@ ensures Bag(_, 0);
    {
        store = new int[cap];
        nelems = 0;
        //@ close Bag(store, 0);
    }
    
    boolean add(int v)
        //@ requires Bag(?s, ?n);
        //@ ensures Bag(_, _) &*& (result == true ? n < s.length : n >= s.length);
    {
        //@ open Bag(s, n);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close Bag(store, nelems);
            return true;
        } else {
            //@ close Bag(store, nelems);
            return false;
        }
    }
}