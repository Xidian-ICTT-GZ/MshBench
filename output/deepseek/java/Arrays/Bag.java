public class Bag {
    int[] store;
    int nelems;

    //@ predicate Bag(int cap) = store |-> ?s &*& s != null &*& s.length == cap &*& array_slice(s, 0, cap, _) &*& nelems |-> 0;
    //@ predicate BagInv() = store |-> ?s &*& s != null &*& array_slice(s, 0, s.length, ?contents) &*& nelems |-> ?n &*& 0 <= n &*& n <= s.length;

    public Bag(int cap)
    //@ requires cap >= 0;
    //@ ensures Bag(cap);
    {
        store = new int[cap];
        nelems = 0;
    }

    boolean add(int v)
    //@ requires BagInv() &*& nelems |-> ?n &*& store |-> ?s &*& s != null &*& array_slice(s, n, s.length, _);
    //@ ensures BagInv() &*& result ? nelems |-> n + 1 &*& array_slice(s, n, s.length, _) : nelems |-> n &*& array_slice(s, n, s.length, _);
    {
        if (nelems < store.length) {
            store[nelems] = v;
            nelems = nelems + 1;
            return true;
        } else {
            return false;
        }
    }
}