public class Bag {
    int[] store;
    int nelems;

    









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
