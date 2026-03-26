public class Bag {
/*@
  predicate Bag_inv(Bag b;) = b.store |-> ?store &*& b.nelems |-> ?nelems &*& store != null &*& nelems >= 0 &*& nelems <= store.length;
@*/
int[] store;
int nelems;

/*@
  requires cap >= 0;
  ensures Bag_inv(this);
@*/
public Bag(int cap)
{
    store = new int[cap];
    nelems = 0;
}

/*@
  requires Bag_inv(this);
  ensures Bag_inv(this) &*& result == (old(nelems) < store.length);
@*/
boolean add(int v)
{
    //@ open Bag_inv(this);
    if(nelems<store.length) {
        store[nelems] = v;
        nelems = nelems+1;
        //@ close Bag_inv(this);
        return true;
    } else {
        //@ close Bag_inv(this);
        return false;
    }
}
}