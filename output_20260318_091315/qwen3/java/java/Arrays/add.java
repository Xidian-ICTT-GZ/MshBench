/*@ predicate bag(Bag b; int cap) =
    b.store |-> ?a &*&
    array_slice(a, 0, cap, ?vs) &*&
    b.nelems |-> ?n &*&
    0 <= n &*& n <= cap;
@*/

public class Bag {
    int[] store;
    int nelems;

    //@ requires true;
    //@ ensures bag(this, result);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
    }

    //@ requires bag(this, ?cap) &*& 0 <= nelems &*& nelems <= cap;
    //@ ensures bag(this, cap) &*& (result == true ? nelems == old_nelems + 1 : nelems == old_nelems);
    boolean add(int v)
    {
        if(nelems<store.length) {
            store[nelems] = v;
            nelems = nelems+1;
            return true;
        } else {
            return false;
        }
    }
}