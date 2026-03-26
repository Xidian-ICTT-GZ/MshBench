public class Bag {
int[] store;
int nelems;

/*@ predicate BagInv(Bag b;) =
      b.store |-> ?store_ &*& b.nelems |-> ?nelems_ &*&
      store_ != null &*&
      0 <= nelems_ &*& nelems_ <= store_.length &*&
      array(store_, int, ?elems) &*& length(store_) == store_.length;
@*/

    //@ requires cap >= 0;
    //@ ensures BagInv(this) &*& nelems == 0 &*& length(store) == cap;
    public Bag(int cap) {
        store = new int[cap];
        nelems = 0;
    }

    /*@ requires BagInv(this) &*&
                 0 <= v &*& true; // just to avoid no arithmetic overflow assumptions
      ensures BagInv(this) &*&
              (result == true &*& nelems == old(nelems) + 1 &*&
               store[old(nelems)] == v &*&
               old(nelems) < length(store))
              ||
              (result == false &*& nelems == old(nelems) &*&
               nelems == length(store));
    @*/
    boolean add(int v) {
        if (nelems < store.length) {
            store[nelems] = v;
            nelems = nelems + 1;
            return true;
        } else {
            return false;
        }
    }
}