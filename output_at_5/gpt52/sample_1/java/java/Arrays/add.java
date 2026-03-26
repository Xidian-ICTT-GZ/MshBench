public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate BagInv() =
        this.store |-> ?a &*& this.nelems |-> ?n &*& a != null &*& 0 <= n &*& n <= a.length;
    @*/

    //@ requires cap >= 0;
    //@ ensures BagInv();
    public Bag(int cap)
        
        
    {
        store = new int[cap];
        nelems = 0;
        //@ close BagInv();
    }

    //@ requires BagInv();
    //@ ensures BagInv();
    boolean add(int v)
        
        
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