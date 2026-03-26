public class Bag {
int[] store;
int nelems;

/*@ 
  predicate bag_state(Bag b; int[] a, int n) = 
    b.store |-> ?s &*& b.nelems |-> ?m &*& s == a &*& m == n &*& 
    0 <= n &*& n <= s.length &*& array_slice(s, 0, n);
    
  predicate array_slice(int[] arr, int from, int to) =
    from == to ? true : array_slice(arr, from, to - 1) &*& arr[to-1] |-> _;
@*/

 //@ requires cap >= 0;
 //@ ensures bag_state(this, store, 0) &*& \length(store) == cap;
public Bag(int cap) {
    store = new int[cap];
    nelems = 0;
}

/*@
  requires bag_state(this, store, ne) &*& 0 <= ne &*& ne <= \length(store);
  ensures  result == true ==> bag_state(this, store, ne + 1) &*& store[ne] |-> v &*& \length(store) == \old(\length(store));
  ensures  result == false ==> bag_state(this, store, ne) &*& ne == \length(store);
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