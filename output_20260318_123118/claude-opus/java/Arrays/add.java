/*@
predicate BagInv(Bag b;) =
    b.store |-> ?arr &*& b.nelems |-> ?n &*&
    arr != null &*& array_slice(arr, 0, arr.length, _) &*&
    0 <= n &*& n <= arr.length;
@*/

public class Bag {
    int[] store;
    int nelems;

    public Bag(int cap)
        //@ requires cap >= 0;
        //@ ensures BagInv(this);
    {
        store = new int[cap];
        nelems = 0;
    }

    boolean add(int v)
        //@ requires BagInv(this);
        //@ ensures BagInv(this);
    {
        //@ open BagInv(this);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close BagInv(this);
            return true;
        } else {
            //@ close BagInv(this);
            return false;
        }
    }
}