public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate BagInv() =
        this.store |-> ?a &*& this.nelems |-> ?n &*& a != null &*& 0 <= n &*& n <= a.length;
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
            store[nelems] = v;
            nelems = nelems+1;
            //@ close BagInv();
            
            return true;
        } else {
            //@ close BagInv();
            
            return false;
        }
    }
}