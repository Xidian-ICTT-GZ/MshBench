public class Bag {
    int[] store;
    int nelems;

    //@ predicate Bag(int cap) = store |-> ?s &*& s != null &*& s.length == cap &*& array_slice(s, 0, cap, _) &*& nelems |-> 0 &*& cap >= 0;
    //@ predicate BagInv() = store |-> ?s &*& s != null &*& array_slice(s, 0, s.length, ?contents) &*& nelems |-> ?n &*& 0 <= n &*& n <= s.length;

    //@ requires cap >= 0;
    //@ ensures Bag(cap);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
    }

    //@ requires BagInv();
    //@ ensures BagInv() &*& (result ? true : true);
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