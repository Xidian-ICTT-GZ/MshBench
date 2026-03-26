public class Bag {
    int[] store;
    int nelems;

    /*@ predicate BagInv(int cap, int n) =
        this.store |-> ?s &*& this.nelems |-> n &*&
        s != null &*& s.length == cap &*&
        0 <= n &*& n <= cap &*&
        array_slice(s, 0, cap, _);
    @*/

    //@ requires cap >= 0;
    //@ ensures BagInv(cap, 0);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
        //@ close BagInv(cap, 0);
    }

    //@ requires BagInv(?cap, ?n);
    //@ ensures result == true &*& BagInv(cap, n + 1) || result == false &*& BagInv(cap, n);
    boolean add(int v)
    {
        //@ open BagInv(cap, n);
        if (nelems < store.length) {
            store[nelems] = v;
            nelems = nelems + 1;
            //@ close BagInv(cap, n + 1);
            return true;
        } else {
            //@ close BagInv(cap, n);
            return false;
        }
    }
}