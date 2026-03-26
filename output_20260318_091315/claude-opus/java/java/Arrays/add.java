public class Bag {
  int[] store;
  int nelems;
  
  /*@ predicate array_slice(int[] a, int lo, int hi, list<int> vs) =
        0 <= lo &*& lo <= hi &*& hi <= a.length &*&
        vs == nil || (length(vs) == hi - lo) &*&
        a != null &*&
        (forall<int> i; lo <= i &*& i < hi; a[i] |-> ?v) &*&
        (vs == nil || 
         (head(vs) == a[lo] &*& array_slice(a, lo+1, hi, tail(vs)))
        );
  @*/
  
  /*@ predicate bag(Bag b; list<int> vs) =
        b.store |-> ?arr &*& b.nelems |-> ?n &*&
        n <= arr.length &*&
        array_slice(arr, 0, n, vs);
  @*/
  
  public Bag(int cap)
    //@ requires 0 <= cap;
    //@ ensures bag(this, nil);
  {
    store = new int[cap];
    nelems = 0;
  }
  
  public boolean add(int v)
    //@ requires bag(this, ?vs);
    //@ ensures bag(this, result ? append(vs, cons(v, nil)) : vs);
  {
    if (nelems < store.length) {
      store[nelems] = v;
      nelems = nelems + 1;
      return true;
    } else {
      return false;
    }
  }
}