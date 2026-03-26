/*@ predicate bag(Bag b; int cap, list<int> vs) =
    b.store |-> ?a &*&
    array_slice(a, 0, vs, _)
    &*& b.nelems |-> length(vs)
    &*& length(vs) <= cap;
@*/

public class Bag {
    int[] store;
    int nelems;

    //@ requires cap >= 0;
    //@ ensures bag(this, cap, nil);
    public Bag(int cap)
    {
        store = new int[cap];
        nelems = 0;
    }

    //@ requires bag(this, ?cap, ?vs) &*& length(vs) < cap;
    //@ ensures bag(this, cap, append(vs, cons(v, nil))) &*& result == true;
    //@ requires bag(this, ?cap, ?vs) &*& length(vs) >= cap;
    //@ ensures bag(this, cap, vs) &*& result == false;
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