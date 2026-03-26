public class Bag {
    int[] store;
    int nelems;

    //@ predicate Bag(int cap) = store |-> ?s &*& s != null &*& s.length == cap &*& nelems |-> ?n &*& 0 <= n &*& n <= cap &*& array_slice(s, 0, n, _) &*& array_slice(s, n, cap, _);
    
    public Bag(int cap)
        //@ requires cap >= 0;
        //@ ensures Bag(cap);
    {
        store = new int[cap];
        nelems = 0;
        //@ close Bag(cap);
    }
    
    boolean add(int v)
        //@ requires Bag(?cap) &*& nelems < cap;
        //@ ensures Bag(cap) &*& result == true;
    {
        //@ open Bag(cap);
        if(nelems<store.length) {
            //@ array_slice_split(store, nelems, nelems+1);
            store[nelems] = v;
            nelems = nelems+1;
            //@ close Bag(cap);
            return true;
        } else {
            
            //@ close Bag(cap);
            return false;
        }
    }
}