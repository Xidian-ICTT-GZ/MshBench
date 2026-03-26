public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate bag() = 
        this.store |-> ?arr &*& this.nelems |-> ?n &*& arr != null &*& 0 <= n &*& n <= arr.length;
    @*/

    //@ requires cap >= 0;
    //@ ensures bag();
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
    }

    //@ requires bag();
    //@ ensures bag() &*& (result ? nelems == old(nelems) + 1 : nelems == old(nelems));
    public boolean add(int v)
    {
        //@ open bag();
        if (nelems < store.length) {
            store[nelems] = v;
            nelems = nelems + 1;
            //@ close bag();
            return true;
        } else {
            //@ close bag();
            return false;
        }
    }
}