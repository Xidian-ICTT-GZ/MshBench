public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate BagInv(Bag b; int[] s, int n) =
        b.store |-> s &*& b.nelems |-> n &*& s != null &*& 0 <= n &*& n <= s.length;
    @*/

    public Bag(int cap)
    //@ requires cap >= 0;
    //@ ensures BagInv(this, ?s, 0);
    {
        store = new int[cap];
        nelems = 0;
        //@ close BagInv(this, store, nelems);
    }
    boolean add(int v)
    //@ requires BagInv(this, ?s, ?n);
    //@ ensures BagInv(this, s, n + (result ? 1 : 0));
    {
        //@ open BagInv(this, s, n);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close BagInv(this, store, nelems);
            return true;
        } else {
            //@ close BagInv(this, store, nelems);
            return false;
        }
    }
}