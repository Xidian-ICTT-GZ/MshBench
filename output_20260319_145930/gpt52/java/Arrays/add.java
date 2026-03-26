public class Bag {
    /*@
    predicate bag(int[] a, int n) =
        this.store |-> a &*& this.nelems |-> n &*& a != null &*& 0 <= n &*& n <= a.length &*&
        array_slice(a, 0, a.length, _);
    @*/

    int[] store;
    int nelems;

    //@ requires cap >= 0;
    //@ ensures bag(?a, 0) &*& a.length == cap;
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
        //@ close bag(store, nelems);
    }

    //@ requires bag(?a, ?n);
    //@ ensures bag(a, n + (result ? 1 : 0)) &*& result == (n < a.length);
    boolean add(int v)
    {
        //@ open bag(a, n);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close bag(a, n + 1);
            return true;
        } else {
            //@ close bag(a, n);
            return false;
        }
    }
}