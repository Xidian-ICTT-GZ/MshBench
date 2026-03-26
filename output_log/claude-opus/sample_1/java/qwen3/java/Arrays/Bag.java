public class Bag {
  int[] store;
  int nelems;

  //@ public predicate bag_state(int[] s, int n) =
  //@   store |-> s &*& nelems |-> n &*& s != null &*& 0 <= n &*& n <= s.length &*& array_slice_int(s, 0, n, _);

  //@ requires cap >= 0;
  //@ ensures bag_state(store, 0) &*& \length(store) == cap;
  public Bag(int cap) {
    store = new int[cap];
    nelems = 0;
  }

  /*@    
    @ requires bag_state(store, nelems);
    @ ensures (result == true &*& bag_state(store, nelems + 1) &*& store[nelems] == v) ||
    @         (result == false &*& bag_state(store, nelems) &*& nelems == \length(store));
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