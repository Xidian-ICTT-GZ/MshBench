public class Bag {
    int[] store;
    int nelems;

    //@ requires cap >= 0;
    //@ ensures store == \result.store &*& \result.nelems == 0 &*&
    //         \length(\result.store) == cap;
    public Bag(int cap) {
        store = new int[cap];
        nelems = 0;
    }

    //@ requires store != null &*& 0 <= nelems &*& nelems <= \length(store);
    //@ ensures (\result == true ==> 
    //           store == \old(store) &*& nelems == \old(nelems) + 1 &*&
    //           \valid(store, \old(nelems)) &*&
    //           store[\old(nelems)] == v &*&
    //           \length(store) == \old(\length(store))) &*&
    //         (\result == false ==> 
    //           store == \old(store) &*& nelems == \old(nelems) &*&
    //           nelems == \length(store));
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