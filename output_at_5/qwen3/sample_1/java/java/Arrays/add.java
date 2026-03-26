public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate valid(Bag this) =
        0 < nelems <= store.length &*&
        store != null &*&
        \forall(int i; 0 <= i < nelems; true);
    @*/

    //@ requires true;
    //@ ensures valid(this);
    public Bag(int cap) {
        store = new int[cap];
        nelems = 0;
    }

    //@ requires valid(this);
    //@ ensures valid(this) &*& (result == true ==> 0 < nelems <= store.length);
    boolean add(int v) {
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            return true;
        } else {
            return false;
        }
    }
}