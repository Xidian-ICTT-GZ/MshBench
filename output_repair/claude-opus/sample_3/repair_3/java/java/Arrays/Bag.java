public class Bag {
    int[] store;
    int nelems;

    /*@ predicate Bag(Bag b, int cap, int n) =
        b.store |-> ?s &*& b.nelems |-> n &*&
        s != null &*& s.length == cap &*&
        0 <= n &*& n <= cap &*&
        array_slice(s, 0, cap, _);
    @*/

    /*@ requires 0 <= cap;
        ensures Bag(this, cap, 0);
    @*/
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
    }

    /*@ requires Bag(this, ?cap, ?n) &*& n < cap;
        ensures Bag(this, cap, n + 1) &*& result == true;
    @*/
    /*@ also
        requires Bag(this, ?cap, ?n) &*& n == cap;
        ensures Bag(this, cap, n) &*& result == false;
    @*/
    boolean add(int v)
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