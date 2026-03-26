public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate bag(int[] s, int n) =
        this.store |-> s &*& this.nelems |-> n &*& s != null &*& 0 <= n &*& n <= s.length;
    @*/

    public Bag(int cap)
        //@ requires 0 <= cap;
        //@ ensures bag(?s, 0) &*& s.length == cap;
    {
        store = new int[cap];
        nelems = 0;
        //@ close bag(store, nelems);
    }
    boolean add(int v)
        //@ requires bag(?s, ?n);
        //@ ensures result ? bag(s, n + 1) : bag(s, n);
    {
        //@ open bag(s, n);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close bag(store, nelems);
            return true;
        } else {
            //@ close bag(store, nelems);
            return false;
        }
    }
}