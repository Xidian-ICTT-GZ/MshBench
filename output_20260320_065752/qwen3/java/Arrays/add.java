public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate Bag_pred(int[] store, int nelems) = 
        store != null &*& 
        0 <= nelems &*& nelems <= store.length;
    @*/

    //@ requires cap >= 0;
    //@ ensures Bag_pred(store, nelems);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
        //@ close Bag_pred(store, nelems);
    }

    //@ requires Bag_pred(store, nelems);
    //@ ensures Bag_pred(store, nelems) &*& result == (nelems < \old(nelems) + 1 ? true : false);
    boolean add(int v)
    {
        //@ open Bag_pred(store, nelems);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close Bag_pred(store, nelems);
            return true;
        } else {
            //@ close Bag_pred(store, nelems);
            return false;
        }
    }
}