public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate BagInv() =
        this.store |-> ?a &*& this.nelems |-> ?n &*& a != null &*& 0 <= n &*& n <= a.length &*& array_slice(a, 0, a.length, _);
    @*/

    public Bag(int cap)
        //@ requires cap >= 0;
        //@ ensures BagInv();
        
        
    {
        store = new int[cap];
        nelems = 0;
        //@ close BagInv();
        
    }
    boolean add(int v)
        //@ requires BagInv();
        //@ ensures BagInv();
        
        
    {
        //@ open BagInv();
        
        if(nelems<store.length) {
            //@ array_slice_split(store, 0, nelems);
            //@ array_slice_split(store, nelems, nelems + 1);
            store[nelems] = v;
            //@ array_slice_join(store, nelems, nelems + 1);
            //@ array_slice_join(store, 0, nelems + 1);
            nelems = nelems+1;
            //@ close BagInv();
            
            return true;
        } else {
            //@ close BagInv();
            
            return false;
        }
    }
}