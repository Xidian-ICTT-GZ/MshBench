public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate BagPred(int cap) =
        store |-> ?s &*& s != null &*& s.length == cap &*& array_slice(s, 0, cap, _) &*&
        nelems |-> ?n &*& 0 <= n &*& n <= cap;
    @*/

    //@ requires 0 <= cap;
    //@ ensures BagPred(cap);
    public Bag(int cap)
        
        
    {
        //@ close BagPred(cap);
        store = new int[cap];
        nelems = 0;
        
    }
    //@ requires BagPred(?cap);
    //@ ensures BagPred(cap) &*& result ? true : true;
    boolean add(int v)
        
        
    {
        //@ open BagPred(cap);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close BagPred(cap);
            return true;
        } else {
            //@ close BagPred(cap);
            return false;
        }
    }
}