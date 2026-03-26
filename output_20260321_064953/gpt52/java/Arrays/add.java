public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate valid() =
        this.store |-> ?a &*& a != null &*& this.nelems |-> ?n &*& 0 <= n &*& n <= a.length;
    @*/

    //@ requires 0 <= cap;
    //@ ensures valid();
    public Bag(int cap)
        
        
    {
        store = new int[cap];
        nelems = 0;
        //@ close valid();
        
    }

    //@ requires valid();
    //@ ensures valid();
    boolean add(int v)
        
        
    {
        //@ open valid();
        
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close valid();
            
            return true;
        } else {
            //@ close valid();
            
            return false;
        }
    }
}