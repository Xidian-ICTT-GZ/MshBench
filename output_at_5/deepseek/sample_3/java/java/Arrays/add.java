public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate Bag() = store |-> ?s &*& s != null &*& nelems |-> ?n &*& 0 <= n &*& n <= s.length &*& array_slice(s, 0, n, _) &*& array_slice(s, n, s.length, _);
    @*/

    public Bag(int cap)
        //@ requires cap >= 0;
        //@ ensures Bag();
    {
        //@ close array_slice(store, 0, cap, _);
        store = new int[cap];
        nelems = 0;
        //@ close Bag();
    }
    boolean add(int v)
        //@ requires Bag();
        //@ ensures Bag();
    {
        //@ open Bag();
        if(nelems<store.length) {
            //@ open array_slice(store, nelems, store.length, _);
            store[nelems] = v;
            //@ close array_slice(store, nelems, store.length, _);
            nelems = nelems+1;
            //@ close Bag();
            return true;
        } else {
            //@ close Bag();
            return false;
        }
    }
}