public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate BagInv(int n) =
        this.store |-> ?s
        &*& this.nelems |-> n
        &*& s != null
        &*& 0 <= n &*& n <= s.length
        &*& array_slice(s, 0, n, ?elems)
        &*& array_slice(s, n, s.length, ?others);
    @*/

    public Bag(int cap)
        //@ requires cap >= 0;
        //@ ensures BagInv(0);
    {
        store = new int[cap];
        nelems = 0;
        //@ close BagInv(0);
    }
    boolean add(int v)
        //@ requires BagInv(?m);
        //@ ensures result ? BagInv(m+1) : BagInv(m);
    {
        //@ open BagInv(?n);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close BagInv(n+1);
            return true;
        } else {
            //@ close BagInv(n);
            return false;
        }
    }
}
