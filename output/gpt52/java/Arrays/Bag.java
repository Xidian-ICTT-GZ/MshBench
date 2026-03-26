public class Bag {
    int[] store;
    int nelems;

    /*@ predicate bag(int[] a, int n) =
            this.store |-> a &*& this.nelems |-> n &*& a != null &*& 0 <= n &*& n <= a.length &*& ints(a, 0, a.length, _);
    @*/

    public Bag(int cap)
    //@ requires 0 <= cap;
    //@ ensures bag(?a, 0) &*& a.length == cap;
    {
        store = new int[cap];
        nelems = 0;
        //@ close bag(store, 0);
    }

    boolean add(int v)
    //@ requires bag(?a, ?n);
    //@ ensures result == true &*& bag(a, n + 1) &*& n < a.length || result == false &*& bag(a, n) &*& n == a.length;
    {
        //@ open bag(a, n);
        if (nelems < store.length) {
            store[nelems] = v;
            nelems = nelems + 1;
            //@ close bag(store, n + 1);
            return true;
        } else {
            //@ close bag(store, n);
            return false;
        }
    }
}