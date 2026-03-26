public class Bag {
    int[] store;
    int nelems;

    /*@
    predicate bag(Bag b; int cap) =
        b.store |-> ?s &*&
        b.nelems |-> ?n &*&
        n >= 0 &*& n <= cap &*&
        chars(s, cap, _);
    @*/

    //@ requires cap >= 0;
    //@ ensures bag(this, cap);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
        //@ close bag(this, cap);
    }

    //@ requires bag(this, ?cap);
    //@ ensures bag(this, cap) &*& result == (nelems < cap);
    boolean add(int v)
    {
        //@ open bag(this, cap);
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            //@ close bag(this, cap);
            return true;
        } else {
            //@ close bag(this, cap);
            return false;
        }
    }
}