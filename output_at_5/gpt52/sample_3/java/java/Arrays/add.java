public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate BagInv() =
        this.store |-> ?a &*& this.nelems |-> ?n &*& a != null &*& 0 <= n &*& n <= a.length &*& ints(a, _);
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
            //@ ints_split(store, nelems);
            store[nelems] = v;
            //@ ints_join(store);
            nelems = nelems+1;
            //@ close BagInv();
            
            return true;
        } else {
            //@ close BagInv();
            
            return false;
        }
    }
}