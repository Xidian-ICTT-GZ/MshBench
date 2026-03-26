public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate valid(Bag this) =
        store != null &*&
        0 <= nelems &*& nelems <= store.length;
    @*/

    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
    }
    
    boolean add(int v)
    {
        
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            
            return true;
        } else {
            
            return false;
        }
    }
}