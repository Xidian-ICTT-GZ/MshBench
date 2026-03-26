public class Bag {
    int[] store;
    int nelems;

    //@ predicate Bag(int cap) = store |-> ?s &*& s != null &*& s.length == cap &*& nelems |-> ?n &*& 0 <= n &*& n <= cap &*& array_slice(s, 0, n, _) &*& array_slice(s, n, cap, _);
    //@ predicate BagInv() = Bag(?cap);

    public Bag(int cap)
        //@ requires cap >= 0;
        //@ ensures Bag(cap);
    {
        store = new int[cap];
        nelems = 0;
        //@ close Bag(cap);
    }
    boolean add(int v)
        //@ requires Bag(?cap) &*& nelems |-> ?n &*& n < cap &*& array_slice(store, n, cap, _);
        //@ ensures Bag(cap) &*& result == true;
        //@ ensures Bag(cap) &*& result == false;
    {
        //@ open Bag(cap);
        if(nelems<store.length) {
            store[nelems] = v;
            //@ array_slice_split(store, nelems, nelems+1);
            nelems = nelems+1;
            //@ close Bag(cap);
            return true;
        } else {
            //@ close Bag(cap);
            return false;
        }
    }
}