/*@
predicate BagInv(Bag b; int[] store, int nelems) =b.store |-> store &*&
    b.nelems |-> nelems &*&
    store != null &*&
    array_slice(store, 0, store.length, _) &*&
    0 <= nelems &*&
    nelems <= store.length;
@*/

public class Bag {
    int[] store;
    int nelems;

    //@ requires cap >= 0;
    //@ ensures BagInv(this, _, 0);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
    }

    //@ requires BagInv(this, ?s, ?n);
    //@ ensures BagInv(this, s, ?n2) &*& (result == true &*& n2 == n + 1 || result == false &*& n2 == n);
    boolean add(int v)
    {
        //@ open BagInv(this, s, n);
        if (nelems < store.length) {
            store[nelems] = v;
            nelems = nelems + 1;
            //@ close BagInv(this, s, nelems);
            return true;
        } else {
            //@ close BagInv(this, s, nelems);
            return false;
        }
    }
}